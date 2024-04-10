package psyq;

//import java.io.BufferedWriter;
//import java.io.File;
//import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.io.File;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import generic.stl.Pair;
import ghidra.app.cmd.disassemble.DisassembleCommand;
import ghidra.app.util.importer.MessageLog;
import ghidra.program.flatapi.FlatProgramAPI;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.listing.CodeUnit;
import ghidra.program.model.listing.Listing;
import ghidra.program.model.listing.Program;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.symbol.Symbol;
import ghidra.util.exception.InvalidInputException;
import ghidra.util.task.TaskMonitor;
import psx.Utils;

public final class SigApplier {
	private final List<PsyqSig> signatures;
	private final String shortLibName;
	private final String gameId;
	private final boolean onlyFirst;
	private final float minEntropy;
	
	public SigApplier(final String gameId, final String libJsonPath, final String patchesFile, boolean onlyFirst, float minEntropy, TaskMonitor monitor) throws IOException {
		this.gameId = gameId.replace("_", "").replace(".", "");
		this.onlyFirst = onlyFirst;
		this.minEntropy = minEntropy;
		
		final File libJsonFile = new File(libJsonPath);
		this.shortLibName = libJsonFile.getName().replace(".json", "");
		
		final JsonArray root = Utils.jsonArrayFromFile(libJsonPath);
		final JsonArray patches = Utils.jsonArrayFromFile(patchesFile);
		
		final String psyLibVersion = libJsonFile.getParentFile().getName();
		final JsonArray patchesObj = findGamePatches(patches, psyLibVersion);
		
		signatures = new ArrayList<>();
//		StringBuilder sb = new StringBuilder();
		
		for (var item : root) {
			final JsonObject itemObj = item.getAsJsonObject();
			final PsyqSig sig = PsyqSig.fromJsonToken(itemObj, patchesObj);
			
			if (sig == null) {
				continue;
			}
			
//			sb.append(String.format("%s/%s: %.2f", this.file, sig.getName(), sig.getEntropy()));
//			sb.append("\n");
			
			signatures.add(sig);
		}
		
//		try (BufferedWriter writer = new BufferedWriter(new FileWriter(new File(file + ".log")))) {
//		    writer.write(sb.toString());
//		}
	}
	
	private JsonArray findGamePatches(final JsonArray patches, final String version) {
		if (patches == null) {
			return null;
		}
		
		for (var patch : patches) {
			final JsonObject patchObj = patch.getAsJsonObject();
			
			for (var game : patchObj.get("names").getAsJsonArray()) {
				final String patchGameName = game.getAsString().replace("_", "").replace(".", "");
				
				if (!patchGameName.equalsIgnoreCase(gameId)) {
					continue;
				}
				
				final JsonArray libs = patchObj.getAsJsonArray("libs");
				
				for (var lib : libs) {
					final JsonObject libObj = lib.getAsJsonObject();
					
					final String patchLibName = libObj.get("name").getAsString();
					
					if (!patchLibName.equalsIgnoreCase(shortLibName)) {
						continue;
					}
					
					final JsonArray patchLibVersions = libObj.get("versions").getAsJsonArray();
					
					for (var libVer : patchLibVersions) {
						final String patchLibVer = libVer.getAsString().replace(".", "");
						
						if (!patchLibVer.equals(version)) {
							continue;
						}
						
						return libObj.getAsJsonArray("objs");
					}
				}
			}
		}
		
		return null;
	}
	
	public List<PsyqSig> getSignatures() {
		return signatures;
	}
	
	public void applySignatures(Program program, Address startAddr, Address endAddr, TaskMonitor monitor, MessageLog log) {
		FlatProgramAPI fpa = new FlatProgramAPI(program);
		Listing listing = program.getListing();
		
		int totalObjs = signatures.size();
		
		monitor.initialize(totalObjs);
		monitor.setMessage("Applying obj symbols...");
		monitor.clearCancelled();
		
		Map<String, Pair<Long, Float>> objsList = new HashMap<>();
		
		for (final PsyqSig sig : signatures) {
			if (monitor.isCancelled()) {
				break;
			}
			
			final MaskedBytes bytes = sig.getSig();
			
			boolean lowEntropy = !bytes.isBiosCall() && (sig.getEntropy() < minEntropy);
			
			final List<Pair<String, Integer>> labels = sig.getLabels();
			
			Address searchAddr = startAddr;
			
			while (!monitor.isCancelled() && searchAddr.compareTo(endAddr) == -1) {
				final Address addr = program.getMemory().findBytes(searchAddr, endAddr, bytes.getBytes(), bytes.getMasks(), true, monitor);
				
				if (addr == null) {
					monitor.incrementProgress(1);
					break;
				}

				if (!sig.isApplied()) {
					objsList.put(sig.getName(), new Pair<>(addr.getOffset(), sig.getEntropy()));
				}
				
				for (var lb : labels) {
					final String lbName = lb.first;
					final int lbOffset = lb.second;
					
					if (lbName.isEmpty()) { // removed label
						continue;
					}
					
					final Address lbAddr = addr.add(lbOffset);
					
					if (listing.getInstructionAt(lbAddr) == null && !lowEntropy && !(sig.isApplied() && onlyFirst)) {
						DisassembleCommand disCmd = new DisassembleCommand(new AddressSet(lbAddr), null);
						disCmd.applyTo(program);
					}
					
					boolean isFunction = !lbName.startsWith("loc_");
					final String newName = String.format("%s_", sig.getName().replace(".", "_"));
					final String newLbName = lbName.replace("text_", newName).replace("loc_", newName);
					
					if (!lowEntropy && !(sig.isApplied() && onlyFirst) && !hasNonDefaultName(program, lbAddr, newLbName)) {
						setFunction(program, fpa, lbAddr, newLbName, isFunction, false, log);
						
						monitor.setMessage(String.format("Symbol %s at 0x%08X", newLbName, lbAddr.getOffset()));
					} else {
						String prevComment = listing.getComment(CodeUnit.PLATE_COMMENT, lbAddr);
						prevComment = (prevComment != null) ? String.format("%s\n", prevComment) : "";
						
						final String newComment = String.format("Possible %s/%s", sig.getName(), newLbName);
						
						if (prevComment.indexOf(newComment) == -1) {
							listing.setComment(lbAddr, CodeUnit.PLATE_COMMENT, String.format("%s%s", prevComment, newComment));
							monitor.setMessage(String.format("Possible symbol %s at 0x%08X", newLbName, lbAddr.getOffset()));
						}
					}
				}

				sig.setApplied(true);
				
				searchAddr = addr.add(4);
				monitor.incrementProgress(1);
			}
		}
		
		if (objsList.size() > 0) {
			log.appendMsg(String.format("Applied OBJs for %s: %d/%d:", shortLibName, objsList.size(), totalObjs));
			
			for (var objName : objsList.entrySet()) {
				var val = objName.getValue();
				log.appendMsg(String.format("\t0x%08X: %s, %.02f entropy", val.first, objName.getKey(), val.second));
			}
		}
	}
	
	private static void disasmInstruction(Program program, Address address) {
		DisassembleCommand cmd = new DisassembleCommand(address, null, true);
		cmd.applyTo(program, TaskMonitor.DUMMY);
	}
	
	public static void setFunction(Program program, FlatProgramAPI fpa, Address address, String name, boolean isFunction, boolean isEntryPoint, MessageLog log) {
		try {
			if (fpa.getInstructionAt(address) == null)
				disasmInstruction(program, address);
			
			if (isFunction) {
				fpa.createFunction(address, name);
			}
			if (isEntryPoint) {
				fpa.addEntryPoint(address);
			}

			if (isFunction && hasNonDefaultName(program, address, null)) {
				return;
			}
			
			program.getSymbolTable().createLabel(address, name, SourceType.IMPORTED);
		} catch (InvalidInputException e) {
			log.appendException(e);
			e.printStackTrace();
		}
	}
	
	private static boolean hasNonDefaultName(Program program, final Address address, final String name) {
		Symbol[] existing = program.getSymbolTable().getSymbols(address);
		
		if (existing.length > 0) {
			for (var sym : existing) {
				if ((sym.getSource() == SourceType.USER_DEFINED) || (sym.getSource() == SourceType.IMPORTED)) {
					return (name == null) ? true : !sym.getName().equals(name);
				}
			}
		}
		
		return false;
	}
}

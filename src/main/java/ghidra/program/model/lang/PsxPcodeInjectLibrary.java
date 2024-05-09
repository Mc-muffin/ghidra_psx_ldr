package ghidra.program.model.lang;

import java.io.IOException;
import ghidra.app.plugin.processors.sleigh.SleighLanguage;
import ghidra.app.plugin.processors.sleigh.template.ConstructTpl;
import ghidra.program.model.address.Address;
import ghidra.program.model.listing.Program;
import ghidra.program.model.mem.MemoryAccessException;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.symbol.SourceType;
import ghidra.util.exception.NotFoundException;

public class PsxPcodeInjectLibrary extends PcodeInjectLibrary {
	
	public PsxPcodeInjectLibrary(SleighLanguage l) {
		super(l);
	}

	public PsxPcodeInjectLibrary(PsxPcodeInjectLibrary op2) {
		super(op2);
	}
	
	@Override
	public PcodeInjectLibrary clone() {
		return new PsxPcodeInjectLibrary(this);
	}
	
	@Override
	public InjectPayload allocateInject(String sourceName, String name, int tp) {
		if (tp == InjectPayload.CALLFIXUP_TYPE) {
			return new InjectPayloadCallfixup(sourceName);
		}
		else if (tp == InjectPayload.CALLOTHERFIXUP_TYPE) {
			return new PsxInjectPayload(sourceName);
		}
		return new InjectPayloadSleigh(name, tp, sourceName);
	}


	/**
	 * At the time of writing, Ghidra does not provide a way to specify a user op as
	 * a "halt" operation, which is needed to stop the decompiler from munging functions
	 * that are separated by break opcodes. Abusing the CALLOTHER spec extension as in this
	 * file and the .cspec is the truly repugnant interim solution to this problem.
	 */
	public class PsxInjectPayload extends InjectPayloadCallother {
		private static final int BRK_HALT = 0x1;
		private static final int BRK_DIVIDE_BY_ZERO = 0x1C00;
		private static final int BRK_DIVIDE_OVERFLOW = 0x1800;
		private static final String BRK_TARGETOP = "trap";
		private static final String KERNEL_EXCEPTION_VECTOR_ADDR = "ram:0x80000080";
		private static final String KERNEL_EXCEPTION_VECTOR_NAME = "Exception_Vector";
		
		private boolean initialized = false;
		private Address addrExceptionVector;

		public PsxInjectPayload(ConstructTpl pcode, InjectPayloadCallother failedPayload) {
			super(pcode, failedPayload);
		}

		public PsxInjectPayload(ConstructTpl pcode, String nm) {
			super(pcode, nm);
		}

		public PsxInjectPayload(String sourceName) {
			super(sourceName);
		}
		
		private synchronized void Init(Program program) {
			if (initialized)
				return;
			
			addrExceptionVector = program.parseAddress(KERNEL_EXCEPTION_VECTOR_ADDR)[0];

			if (program.getFunctionManager().getFunctionAt(addrExceptionVector) == null) {
				boolean commit = false;
				int id = program.startTransaction("Create exception vector function");
				try {
					program.getFunctionManager().createFunction(
							KERNEL_EXCEPTION_VECTOR_NAME,
							addrExceptionVector, 
							program.getAddressFactory().getAddressSet(addrExceptionVector, addrExceptionVector.add(0x10)),
							SourceType.ANALYSIS);
					
					commit = true;
				} catch (Exception e) {
					e.printStackTrace();
				}
				finally {
					program.endTransaction(id, commit);
				}
			}

			initialized = true;
		}

		@Override
		public PcodeOp[] getPcode(Program program, InjectContext con)
				throws UnknownInstructionException, MemoryAccessException, IOException, NotFoundException {
			if (!initialized)
				Init(program);
				
			if (name.equals(BRK_TARGETOP)) {
				if ((con.inputlist == null) || (con.inputlist.size() <= 0) || !(con.inputlist.get(0).isConstant()))
					throw new UnknownInstructionException();
				
				int brkCode = (int)con.inputlist.get(0).getOffset();
				
				switch (brkCode) {
					case BRK_HALT, BRK_DIVIDE_BY_ZERO, BRK_DIVIDE_OVERFLOW:
						var addr = con.baseAddr;
						var brkInst = program.getListing().getInstructionAt(addr);
						if (brkInst.isFallThroughOverridden())
							break;

						boolean commit = false;
						int id = program.startTransaction("Set halt fallthrough");
						try {
							brkInst.setFallThrough(addrExceptionVector);
							commit = true;
						}
						finally {
							program.endTransaction(id, commit);
						}

						break;
				}
			}

			return super.getPcode(program, con);
		}
		
		@Override
		public boolean isFallThru() {
			return true; // Technically true despite modelling a halt instruction.
		}
	}
}

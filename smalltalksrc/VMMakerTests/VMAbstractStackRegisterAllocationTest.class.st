Class {
	#name : 'VMAbstractStackRegisterAllocationTest',
	#superclass : 'VMStackToRegisterMappingCogitTest',
	#pools : [
		'CogRTLOpcodes',
		'VMStackFrameOffsets'
	],
	#category : 'VMMakerTests-JitTests',
	#package : 'VMMakerTests',
	#tag : 'JitTests'
}

{ #category : 'running' }
VMAbstractStackRegisterAllocationTest >> setUp [

	super setUp.
	"Start with an empty stack, always has at least self in the fixed part"
	
	" | self        |  \
	  | arg0        |   |
	  | ...         |   |
	  | argn        |   - Fixed part per frame. Pops should not touch this part
	  | temp0       |   |
	  | ...         |   |
	  | temp1       |  /
	  | stackEntry0 |  \
	  | ...         |   - Variable part per frame. Push and pop act here.
	  | stackEntryn |  /
	"
	
	cogit methodOrBlockNumTemps: 0.
	cogit initSimStackPointer: 0.
	
	"Initialize the self stack entry as spilled relative to the frame pointer"
	cogit simSelf
		type: SSBaseOffset;
		spilled: true;
		registerr: FPReg;
		offset: FoxMFReceiver;
		liveRegister: NoReg.
	
	"Spilling only works on frameful compilation"
	cogit needsFrame: true
]

{ #category : 'tests' }
VMAbstractStackRegisterAllocationTest >> testReceiverIsInRegisterBeforeRegisterAllocation [

	self assert: cogit ssSize equals: 1.
	self assert: cogit ssTop equals: cogit simSelf.
	self assert: cogit ssTop spilled
]

{ #category : 'tests' }
VMAbstractStackRegisterAllocationTest >> testRegisterAllocationShouldMoveConstantIntoMemoryIfSpilling [

	cogit ssPushConstant: 7.
	cogit ssAllocateRegistersForceSpilling: true.

	"Check the stack was modified"
	self assert: cogit ssSize equals: 2.
	self assert: cogit ssTop spilled.
	self assert: cogit ssTop type equals: SSConstant.

	"And that the last generated instruction was a constant push.
	This should generate a PushCq(7)"
	self assert: cogit lastOpcode opcode equals: PushCq.
	self assert: (cogit lastOpcode operands at: 0) equals: 7
]

{ #category : 'tests' }
VMAbstractStackRegisterAllocationTest >> testRegisterAllocationShouldMoveConstantIntoRegister [

	cogit ssPushConstant: 7.
	cogit ssAllocateRegisters.

	"Check the stack was modified"
	self assert: cogit ssSize equals: 2.
	self assert: cogit ssTop type equals: SSRegister.

	"And that the last generated instruction was a move of the constant to the register in the stack
	This should generate a MoveCqR(7, TheRegisterInStack)"
	self assert: cogit lastOpcode opcode equals: MoveCqR.
	self assert: (cogit lastOpcode operands at: 0) equals: 7.
	self
		assert: (cogit lastOpcode operands at: 1)
		equals: cogit ssTop registerr
]

{ #category : 'tests' }
VMAbstractStackRegisterAllocationTest >> testRegisterAllocationShouldNotAffectTopSpilled [

	cogit ssAllocateRegisters.

	self assert: cogit ssSize equals: 1.
	self assert: cogit ssTop equals: cogit simSelf.
	self assert: cogit ssTop spilled
]

{ #category : 'tests' }
VMAbstractStackRegisterAllocationTest >> testRegisterAllocationShouldSpillInTheRightOrder [

	| firstInstruction lastInstruction |
	cogit ssPushConstant: 7.
	cogit ssPushConstant: 42.
	cogit ssAllocateRegistersForceSpilling: true.

	"Expect PushCq(7)"
	firstInstruction := cogit abstractInstructionAt: cogit opcodeIndex - 2.
	self assert: firstInstruction opcode equals: PushCq.
	self assert: (firstInstruction operands at: 0) equals: 7.

	"Expect PushCq(42)"
	lastInstruction := cogit abstractInstructionAt: cogit opcodeIndex - 1.
	self assert: lastInstruction opcode equals: PushCq.
	self assert: (lastInstruction operands at: 0) equals: 42
]

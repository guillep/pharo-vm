Class {
	#name : 'VMAbstractStackRegisterAllocationTest',
	#superclass : 'VMStackToRegisterMappingCogitTest',
	#instVars : [
		'currentAbstractStack'
	],
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
	cogit currentAbstractStack simSelf
		type: SSBaseOffset;
		spilled: true;
		registerr: FPReg;
		offset: FoxMFReceiver;
		liveRegister: NoReg.
	
	"Spilling only works on frameful compilation"
	cogit needsFrame: true.
	
	currentAbstractStack := cogit currentAbstractStack.
]

{ #category : 'tests' }
VMAbstractStackRegisterAllocationTest >> testReceiverIsInRegisterBeforeRegisterAllocation [

	self assert: currentAbstractStack ssSize equals: 1.
	self assert: currentAbstractStack ssTop equals: currentAbstractStack simSelf.
	self assert: currentAbstractStack ssTop spilled
]

{ #category : 'tests' }
VMAbstractStackRegisterAllocationTest >> testRegisterAllocationShouldMoveConstantIntoMemoryIfSpilling [

	currentAbstractStack ssPushConstant: 7.
	currentAbstractStack ssAllocateRegistersForceSpilling: true.

	"Check the stack was modified"
	self assert: currentAbstractStack ssSize equals: 2.
	self assert: currentAbstractStack ssTop spilled.
	self assert: currentAbstractStack ssTop type equals: SSConstant.

	"And that the last generated instruction was a constant push.
	This should generate a PushCq(7)"
	self assert: cogit lastOpcode opcode equals: PushCq.
	self assert: (cogit lastOpcode operands at: 0) equals: 7
]

{ #category : 'tests' }
VMAbstractStackRegisterAllocationTest >> testRegisterAllocationShouldMoveConstantIntoRegister [

	currentAbstractStack ssPushConstant: 7.
	currentAbstractStack ssAllocateRegisters.

	"Check the stack was modified"
	self assert: currentAbstractStack ssSize equals: 2.
	self assert: currentAbstractStack ssTop type equals: SSRegister.

	"And that the last generated instruction was a move of the constant to the register in the stack
	This should generate a MoveCqR(7, TheRegisterInStack)"
	self assert: cogit lastOpcode opcode equals: MoveCqR.
	self assert: (cogit lastOpcode operands at: 0) equals: 7.
	self
		assert: (cogit lastOpcode operands at: 1)
		equals: currentAbstractStack ssTop registerr
]

{ #category : 'tests' }
VMAbstractStackRegisterAllocationTest >> testRegisterAllocationShouldNotAffectTopSpilled [

	currentAbstractStack ssAllocateRegisters.

	self assert: currentAbstractStack ssSize equals: 1.
	self assert: currentAbstractStack ssTop equals: currentAbstractStack simSelf.
	self assert: currentAbstractStack ssTop spilled
]

{ #category : 'tests' }
VMAbstractStackRegisterAllocationTest >> testRegisterAllocationShouldSpillInTheRightOrder [

	| firstInstruction lastInstruction |
	currentAbstractStack ssPushConstant: 7.
	currentAbstractStack ssPushConstant: 42.
	currentAbstractStack ssAllocateRegistersForceSpilling: true.

	"Expect PushCq(7)"
	firstInstruction := cogit abstractInstructionAt: cogit opcodeIndex - 2.
	self assert: firstInstruction opcode equals: PushCq.
	self assert: (firstInstruction operands at: 0) equals: 7.

	"Expect PushCq(42)"
	lastInstruction := cogit abstractInstructionAt: cogit opcodeIndex - 1.
	self assert: lastInstruction opcode equals: PushCq.
	self assert: (lastInstruction operands at: 0) equals: 42
]

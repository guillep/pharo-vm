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

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeLiveRegisterAndConstant [

	| branchIncomingStack fallthroughStack i1 i2 someFreeRegister |
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	fallthroughStack := cogit currentAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra1Reg.
	branchIncomingStack ssPushRegister: Extra0Reg.
	
	"Extra0Reg is live! We should generate a swap!"
	fallthroughStack ssPushRegister: Extra0Reg.
	fallthroughStack ssPushConstant: 17.
	
	someFreeRegister := fallthroughStack availableRegOrNoneNotConflictingWith: 0.
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack top was merged into a register!"
	self deny: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSRegister.
	self assert: cogit currentAbstractStack ssTop registerr equals: Extra0Reg.

	"The entry before is now in Extra1Reg"
	self deny: (cogit currentAbstractStack simStackAt: 1) spilled.
	self assert: (cogit currentAbstractStack simStackAt: 1) type equals: SSRegister.
	self assert: (cogit currentAbstractStack simStackAt: 1) registerr equals: Extra1Reg.
	
	"The last generated instructions should be

		Extra1Reg := Extra0Reg. -> we free the Extra0Reg
		Extra0Reg := 17."

	i2 := cogit abstractInstructionAt: cogit opcodeIndex - 2.
	self assert: i2 opcode equals: MoveRR.
	self assert: (i2 operands at: 0) equals: Extra0Reg.
	self assert: (i2 operands at: 1) equals: Extra1Reg.
		
	i1 := cogit abstractInstructionAt: cogit opcodeIndex - 1.
	self assert: i1 opcode equals: MoveCqR.
	self assert: (i1 operands at: 0) equals: 17.
	self assert: (i1 operands at: 1) equals: Extra0Reg.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeLiveRegisterAndConstantAndConflictOnSecondSlot [

	| branchIncomingStack fallthroughStack i1 i2 i3 someFreeRegister |
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	fallthroughStack := cogit currentAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra2Reg.
	branchIncomingStack ssPushRegister: Extra0Reg.
	
	"Extra0Reg is live! We should generate a swap!"
	fallthroughStack ssPushRegister: Extra0Reg.
	fallthroughStack ssPushConstant: 17.
	
	someFreeRegister := fallthroughStack availableRegOrNoneNotConflictingWith: 0.
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack top was merged into a register!"
	self deny: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSRegister.
	self assert: cogit currentAbstractStack ssTop registerr equals: Extra0Reg.

	"The entry before is now in Extra2Reg"
	self deny: (cogit currentAbstractStack simStackAt: 1) spilled.
	self assert: (cogit currentAbstractStack simStackAt: 1) type equals: SSRegister.
	self assert: (cogit currentAbstractStack simStackAt: 1) registerr equals: Extra2Reg.
	
	"The last generated instructions should be

		Extra1Reg := Extra0Reg. -> we free the Extra0Reg
		Extra0Reg := 17.
		Extra2Reg := Extra1Reg"

	i2 := cogit abstractInstructionAt: cogit opcodeIndex - 3.
	self assert: i2 opcode equals: MoveRR.
	self assert: (i2 operands at: 0) equals: Extra0Reg.
	self assert: (i2 operands at: 1) equals: Extra1Reg.
		
	i1 := cogit abstractInstructionAt: cogit opcodeIndex - 2.
	self assert: i1 opcode equals: MoveCqR.
	self assert: (i1 operands at: 0) equals: 17.
	self assert: (i1 operands at: 1) equals: Extra0Reg.
	
	i3 := cogit abstractInstructionAt: cogit opcodeIndex - 1.
	self assert: i3 opcode equals: MoveRR.
	self assert: (i3 operands at: 0) equals: Extra1Reg.
	self assert: (i3 operands at: 1) equals: Extra2Reg.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeLiveRegisterAndMemory [

	| branchIncomingStack fallthroughStack opcodeBeforeMerge base offset i2 i1 i3 |
	opcodeBeforeMerge := cogit lastOpcode.
	
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	fallthroughStack := cogit currentAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra2Reg.
	branchIncomingStack ssPushRegister: Extra0Reg.

	fallthroughStack ssPushRegister: Extra0Reg.	
	fallthroughStack ssPushBase: (base := FPReg) offset: (offset := 0).
	
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack top was merged into a register!"
	self deny: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSRegister.
	self assert: cogit currentAbstractStack ssTop registerr equals: Extra0Reg.

	"The entry before is now in Extra2Reg"
	self deny: (cogit currentAbstractStack simStackAt: 1) spilled.
	self assert: (cogit currentAbstractStack simStackAt: 1) type equals: SSRegister.
	self assert: (cogit currentAbstractStack simStackAt: 1) registerr equals: Extra2Reg.
	
	"The last generated instructions should be

		Extra1Reg := Extra0Reg. -> we free the Extra0Reg
		Extra0Reg := Load [FP,offset].
		Extra2Reg := Extra1Reg."
	
	i2 := cogit abstractInstructionAt: cogit opcodeIndex - 3.
	self assert: i2 opcode equals: MoveRR.
	self assert: (i2 operands at: 0) equals: Extra0Reg.
	self assert: (i2 operands at: 1) equals: Extra1Reg.
		
	i1 := cogit abstractInstructionAt: cogit opcodeIndex - 2.
	self assert: i1 opcode equals: MoveMwrR.
	self assert: (i1 operands at: 0) equals: offset.
	self assert: (i1 operands at: 1) equals: base.
	self assert: (i1 operands at: 2) equals: Extra0Reg.
	
	i3 := cogit abstractInstructionAt: cogit opcodeIndex - 1.
	self assert: i3 opcode equals: MoveRR.
	self assert: (i3 operands at: 0) equals: Extra1Reg.
	self assert: (i3 operands at: 1) equals: Extra2Reg.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeLiveRegisterAndOtherRegister [

	| branchIncomingStack fallthroughStack opcodeBeforeMerge i1 i3 |
	opcodeBeforeMerge := cogit lastOpcode.
	
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	fallthroughStack := cogit currentAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra2Reg.
	branchIncomingStack ssPushRegister: Extra0Reg.

	fallthroughStack ssPushRegister: Extra0Reg.	
	fallthroughStack ssPushRegister: Extra1Reg.
	
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack top was merged into a register!"
	self deny: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSRegister.
	self assert: cogit currentAbstractStack ssTop registerr equals: Extra0Reg.

	"The entry before is now in Extra2Reg"
	self deny: (cogit currentAbstractStack simStackAt: 1) spilled.
	self assert: (cogit currentAbstractStack simStackAt: 1) type equals: SSRegister.
	self assert: (cogit currentAbstractStack simStackAt: 1) registerr equals: Extra2Reg.
	
	"The last generated instructions should be

		Extra2Reg := Extra0Reg. -> we free the Extra0Reg
		Extra0Reg := Extra1Reg"
	
	i1 := cogit abstractInstructionAt: cogit opcodeIndex - 2.
	self assert: i1 opcode equals: MoveRR.
	self assert: (i1 operands at: 0) equals: Extra0Reg.
	self assert: (i1 operands at: 1) equals: Extra2Reg.
	
	i3 := cogit abstractInstructionAt: cogit opcodeIndex - 1.
	self assert: i3 opcode equals: MoveRR.
	self assert: (i3 operands at: 0) equals: Extra1Reg.
	self assert: (i3 operands at: 1) equals: Extra0Reg.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeLiveRegisterAndSameRegister [

	| branchIncomingStack fallthroughStack opcodeBeforeMerge i1 |
	opcodeBeforeMerge := cogit lastOpcode.
	
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	fallthroughStack := cogit currentAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra2Reg.
	branchIncomingStack ssPushRegister: Extra1Reg.

	fallthroughStack ssPushRegister: Extra2Reg.	
	fallthroughStack ssPushRegister: Extra0Reg.
	
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack top was merged into a register!"
	self deny: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSRegister.
	self assert: cogit currentAbstractStack ssTop registerr equals: Extra1Reg.

	"The entry before is now in Extra2Reg"
	self deny: (cogit currentAbstractStack simStackAt: 1) spilled.
	self assert: (cogit currentAbstractStack simStackAt: 1) type equals: SSRegister.
	self assert: (cogit currentAbstractStack simStackAt: 1) registerr equals: Extra2Reg.
	
	"The last generated instructions should be

		Extra1Reg := Extra0Reg"
	
	i1 := cogit abstractInstructionAt: cogit opcodeIndex - 1.
	self assert: i1 opcode equals: MoveRR.
	self assert: (i1 operands at: 0) equals: Extra0Reg.
	self assert: (i1 operands at: 1) equals: Extra1Reg.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeNotLiveRegisterAndConstant [

	| branchIncomingStack fallthroughStack |
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	fallthroughStack := cogit currentAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra0Reg.
	fallthroughStack ssPushConstant: 17.
	
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack was merged into a register!"
	self deny: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSRegister.
	self assert: cogit currentAbstractStack ssTop registerr equals: Extra0Reg.
	
	"The last generated instruction should be a copy Extra0Reg := 17"
	self assert: cogit lastOpcode opcode equals: MoveCqR.
	self assert: (cogit lastOpcode operands at: 0) equals: 17.
	self assert: (cogit lastOpcode operands at: 1) equals: Extra0Reg
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeNotLiveRegisterAndMemory [

	| branchIncomingStack fallthroughStack opcodeBeforeMerge base offset |
	opcodeBeforeMerge := cogit lastOpcode.
	
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	fallthroughStack := cogit currentAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra0Reg.
	fallthroughStack ssPushBase: (base := FPReg) offset: (offset := 0).
	
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack was merged into the incoming register Extra0Reg!"
	self deny: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSRegister.
	self assert: cogit currentAbstractStack ssTop registerr equals: Extra0Reg.
	
	"The last generated instruction should be a copy Extra0Reg := LOAD [FP,0]"
	self assert: cogit lastOpcode opcode equals: MoveMwrR.
	self assert: (cogit lastOpcode operands at: 0) equals: offset.
	self assert: (cogit lastOpcode operands at: 1) equals: base.
	self assert: (cogit lastOpcode operands at: 2) equals: Extra0Reg.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeNotLiveRegisterAndOtherRegister [

	| branchIncomingStack fallthroughStack opcodeBeforeMerge |
	opcodeBeforeMerge := cogit lastOpcode.
	
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	fallthroughStack := cogit currentAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra0Reg.
	fallthroughStack ssPushRegister: Extra1Reg.
	
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack was merged into the incoming register Extra0Reg!"
	self deny: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSRegister.
	self assert: cogit currentAbstractStack ssTop registerr equals: Extra0Reg.
	
	"The last generated instruction should be a copy Extra0Reg := Extra1Reg"
	self assert: cogit lastOpcode opcode equals: MoveRR.
	self assert: (cogit lastOpcode operands at: 0) equals: Extra1Reg.
	self assert: (cogit lastOpcode operands at: 1) equals: Extra0Reg
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeNotLiveRegisterAndSameRegister [

	| branchIncomingStack fallthroughStack opcodeBeforeMerge |
	opcodeBeforeMerge := cogit lastOpcode.
	
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	fallthroughStack := cogit currentAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra0Reg.
	fallthroughStack ssPushRegister: Extra0Reg.
	
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack was merged into a register!"
	self deny: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSRegister.
	self assert: cogit currentAbstractStack ssTop registerr equals: Extra0Reg.
	
	"The last generated instruction is the same as before"
	self assert: cogit lastOpcode equals: opcodeBeforeMerge
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeRegisterAndSpilledConstant [

	"This test is for non live registers.
	There are no cases for merging live registers with spilled slots.
	By construction, if a slot is spilled, all the stack slots above are spilled too
		=> no live registers are above it!"

	| branchIncomingStack fallthroughStack opcodeBeforeMerge |
	opcodeBeforeMerge := cogit lastOpcode.
	
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	fallthroughStack := cogit currentAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra0Reg.
	fallthroughStack ssPushConstant: 17.
	fallthroughStack ssSpillStack.
	
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack was merged into the incoming register Extra0Reg!
	The spilling should be the same in both stacks"
	self assert: cogit currentAbstractStack ssTop spilled equals: branchIncomingStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSRegister.
	self assert: cogit currentAbstractStack ssTop registerr equals: Extra0Reg.
	
	"The last generated instruction should be a copy Extra0Reg := Pop"
	self assert: cogit lastOpcode opcode equals: PopR.
	self assert: (cogit lastOpcode operands at: 0) equals: Extra0Reg.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeRegisterAndSpilledMemoryAccess [

	"This test is for non live registers.
	There are no cases for merging live registers with spilled slots.
	By construction, if a slot is spilled, all the stack slots above are spilled too
		=> no live registers are above it!"

	| branchIncomingStack fallthroughStack opcodeBeforeMerge base offset |
	opcodeBeforeMerge := cogit lastOpcode.
	
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	fallthroughStack := cogit currentAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra0Reg.
	fallthroughStack ssPushBase: (base := FPReg) offset: (offset := 0).
	fallthroughStack ssSpillStack.
	
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack was merged into the incoming register Extra0Reg!
	The spilling should be the same in both stacks"
	self assert: cogit currentAbstractStack ssTop spilled equals: branchIncomingStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSRegister.
	self assert: cogit currentAbstractStack ssTop registerr equals: Extra0Reg.
	
	"The last generated instruction should be a copy Extra0Reg := Pop"
	self assert: cogit lastOpcode opcode equals: PopR.
	self assert: (cogit lastOpcode operands at: 0) equals: Extra0Reg.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeSpillSlotAndConstant [

	| branchIncomingStack fallthroughStack i1 i2 |
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra0Reg.
	branchIncomingStack ssSpillStack.

	fallthroughStack := cogit currentAbstractStack.
	fallthroughStack ssPushConstant: 17.
	
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack was merged into a spill slot!"
	self assert: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSSpill.
	self assert: cogit currentAbstractStack ssTop base equals: FPReg.
	self assert: cogit currentAbstractStack ssTop offset equals: -32.
	
	"The last generated instructions should be
		TempReg := 17.
		Store TempReg [FPReg, -32]"
		
	i1 := cogit abstractInstructionAt: cogit opcodeIndex - 2.
	self assert: i1 opcode equals: MoveCqR.
	self assert: (i1 operands at: 0) equals: 17.
	self assert: (i1 operands at: 1) equals: TempReg.

	i2 := cogit abstractInstructionAt: cogit opcodeIndex - 1.
	self assert: i2 opcode equals: MoveRMwr.
	self assert: (i2 operands at: 0) equals: TempReg.
	self assert: (i2 operands at: 1) equals: -32.
	self assert: (i2 operands at: 2) equals: FPReg.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeSpillSlotAndMemory [

	| branchIncomingStack fallthroughStack i1 i2 |	
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra0Reg.
	branchIncomingStack ssSpillStack.

	fallthroughStack := cogit currentAbstractStack.
	fallthroughStack ssPushBase: FPReg offset: 17.

	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack was merged into a spill slot!"
	self assert: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSSpill.
	self assert: cogit currentAbstractStack ssTop base equals: FPReg.
	self assert: cogit currentAbstractStack ssTop offset equals: -32.
	
	"The last generated instructions should be
		TempReg := Load [FPReg, 17].
		Store TempReg [FPReg, -32]"
		
	i1 := cogit abstractInstructionAt: cogit opcodeIndex - 2.
	self assert: i1 opcode equals: MoveMwrR.
	self assert: (i1 operands at: 0) equals: 17.
	self assert: (i1 operands at: 1) equals: FPReg.
	self assert: (i1 operands at: 2) equals: TempReg.

	i2 := cogit abstractInstructionAt: cogit opcodeIndex - 1.
	self assert: i2 opcode equals: MoveRMwr.
	self assert: (i2 operands at: 0) equals: TempReg.
	self assert: (i2 operands at: 1) equals: -32.
	self assert: (i2 operands at: 2) equals: FPReg.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeSpillSlotAndNotLiveRegister [

	| branchIncomingStack fallthroughStack i2 |
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra0Reg.
	branchIncomingStack ssSpillStack.

	fallthroughStack := cogit currentAbstractStack.
	fallthroughStack ssPushRegister: FPReg.
	
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack was merged into a spill slot!"
	self assert: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSSpill.
	self assert: cogit currentAbstractStack ssTop base equals: FPReg.
	self assert: cogit currentAbstractStack ssTop offset equals: -32.
	
	"The last generated instructions should be
		Store FPReg [FPReg, -32]"
	i2 := cogit abstractInstructionAt: cogit opcodeIndex - 1.
	self assert: i2 opcode equals: MoveRMwr.
	self assert: (i2 operands at: 0) equals: FPReg.
	self assert: (i2 operands at: 1) equals: -32.
	self assert: (i2 operands at: 2) equals: FPReg.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeSpillSlotAndSpillSlot [

	| branchIncomingStack fallthroughStack |	
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra0Reg.
	branchIncomingStack ssSpillStack.

	fallthroughStack := cogit currentAbstractStack.
	fallthroughStack ssPushBase: FPReg offset: 17.
	fallthroughStack ssSpillStack.
	
	"Canary nop to check that no instructions were generated"
	cogit Nop.
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack was merged into a spill slot!"
	self assert: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSSpill.
	self assert: cogit currentAbstractStack ssTop base equals: FPReg.
	self assert: cogit currentAbstractStack ssTop offset equals: -32.
	
	"No instructions should be generated.
	Check that the canary instruction is there."
	self assert: cogit lastOpcode opcode equals: Nop.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testMergeSpillSlotAndSpilledConstant [

	| branchIncomingStack fallthroughStack |
	branchIncomingStack := cogit currentAbstractStack.
	cogit copyAbstractStack.
	
	branchIncomingStack ssPushRegister: Extra0Reg.
	branchIncomingStack ssSpillStack.

	fallthroughStack := cogit currentAbstractStack.
	fallthroughStack ssPushConstant: 17.
	fallthroughStack ssSpillStack.
	
	"Canary nop to check that no instructions were generated"
	cogit Nop.
	cogit mergeIncomingBranchStack: branchIncomingStack.
	
	"The abstract stack was merged into a spill slot!"
	self assert: cogit currentAbstractStack ssTop spilled.
	self assert: cogit currentAbstractStack ssTop type equals: SSSpill.
	self assert: cogit currentAbstractStack ssTop base equals: FPReg.
	self assert: cogit currentAbstractStack ssTop offset equals: -32.
	
	"No instructions should be generated.
	Check that the canary instruction is there."
	self assert: cogit lastOpcode opcode equals: Nop.
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testPopInCopyDoesNotAffectOriginal [

	| previousStack sizeBefore |
	previousStack := cogit currentAbstractStack.
	previousStack ssPushConstant: 17.
	
	sizeBefore := cogit currentAbstractStack ssSize.
	cogit copyAbstractStack.
	cogit currentAbstractStack ssPop: 1.
	
	self assert: previousStack ssSize equals: sizeBefore
]

{ #category : 'as yet unclassified' }
VMAbstractStackRegisterAllocationTest >> testPushInCopyDoesNotAffectOriginal [

	| previousStack sizeBefore |
	previousStack := cogit currentAbstractStack.
	sizeBefore := cogit currentAbstractStack ssSize.
	cogit copyAbstractStack.
	cogit currentAbstractStack ssPushConstant: 17.
	
	self assert: previousStack ssSize equals: sizeBefore
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

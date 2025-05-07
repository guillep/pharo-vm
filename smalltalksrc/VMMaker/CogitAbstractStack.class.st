Class {
	#name : 'CogitAbstractStack',
	#superclass : 'VMStructType',
	#instVars : [
		'simStackPtr',
		'simSpillBase',
		'simStack',
		'cogit'
	],
	#pools : [
		'CogAbstractRegisters',
		'CogCompilationConstants',
		'VMBytecodeConstants'
	],
	#category : 'VMMaker-JIT',
	#package : 'VMMaker',
	#tag : 'JIT'
}

{ #category : 'simulation stack' }
CogitAbstractStack >> allocateFloatRegNotConflictingWith: regMask [
	| reg |
	"if there's a free register, use it"
	reg := self backEnd availableFloatRegisterOrNoneFor: (self liveFloatRegisters bitOr: regMask).
	reg = NoReg ifTrue: "No free register, choose one that does not conflict with regMask"
		[reg := self freeAnyFloatRegNotConflictingWith: regMask].
	^ reg
]

{ #category : 'simulation stack' }
CogitAbstractStack >> allocateRegForStackEntryAt: index [
	"If the stack entry is already in a register, answers it,
	else allocate a new register for it"
	<inline: true>
	^ self allocateRegForStackEntryAt: index notConflictingWith: 0
	
]

{ #category : 'simulation stack' }
CogitAbstractStack >> allocateRegForStackEntryAt: index notConflictingWith: regMask [
	"If the stack entry is already in a register not conflicting with regMask, answers it,
	else allocate a new register not conflicting with reg mask"
	<var: #stackEntry type: #'CogSimStackEntry *'>
	<returnTypeC: #'signed char'>
	| stackEntry mask |
	stackEntry := self ssValue: index.
	mask := stackEntry registerMaskOrNone.
	(mask ~= 0 and: [mask noMask: regMask]) ifTrue: 
		[self flag: #TODO.
		"When one does pushDup on a SSRegister
		 followed by an operation reusing the register 
		 but mutating the value of the register, then the value that was 
		 dup is now refering to the register with a mutated value which
		 is incorrect. This problem is serious as it can happen also with 
		 multiple unsafe instructions (no dup involved)
		 This is not a problem if the operation reusing the register is not 
		 mutating the value of if all the dup values are used in the same 
		 operation.
		 => I think we should introduce allocateRegMutatingStackEntryAt:
		notConflictingWith:upThrough:, used by operations mutating the reg
		value and flushing partially the stack if somewhere between simSpill
		and the ssEntries used by the operation someone uses also the same
		register."
		 ^stackEntry registerOrNone].
	^self allocateRegNotConflictingWith: regMask
]

{ #category : 'simulation stack' }
CogitAbstractStack >> allocateRegForStackTopThreeEntriesInto: trinaryBlock thirdIsReceiver: thirdIsReceiver [
	"Answers registers for the 3 top values on stack. If the values are already in registers, answers
	these registers, else allocate registers not conflicting with each others.
	If thirdIsReceiver is true, allocate ReceiverResultReg for stackTop - 2 (for ceStoreCheck)."
	<inline: true>
	| topRegistersMask rTop rNext rThird |
	
	topRegistersMask := 0.
	rTop := rNext := rThird := NoReg.
	
	(self ssTop registerOrNone ~= NoReg and: [ thirdIsReceiver not or: [ self ssTop registerOrNone ~= ReceiverResultReg ] ]) ifTrue: 
		[ topRegistersMask := self registerMaskFor: (rTop := self ssTop registerOrNone)].
	((self ssValue: 1) registerOrNone ~= NoReg and: [ thirdIsReceiver not or: [ (self ssValue: 1) registerOrNone ~= ReceiverResultReg ] ]) ifTrue: 
		[ topRegistersMask := topRegistersMask bitOr: (self registerMaskFor: (rNext := (self ssValue: 1) registerOrNone))].
	((self ssValue: 2) registerOrNone ~= NoReg and: [thirdIsReceiver not or: [ (self ssValue: 2) registerOrNone = ReceiverResultReg ] ]) ifTrue: 
		[ topRegistersMask := topRegistersMask bitOr: (self registerMaskFor: (rThird := (self ssValue: 2) registerOrNone))].
	
	rThird = NoReg ifTrue:
		[ thirdIsReceiver 
			ifTrue:
				[ rThird := ReceiverResultReg.  "Free ReceiverResultReg if it was not free"
				self ssAllocateRequiredReg: ReceiverResultReg.
				self voidReceiverResultRegContainsSelf ]
			ifFalse: [ rThird := self allocateRegNotConflictingWith: topRegistersMask ].
		topRegistersMask := topRegistersMask bitOr: (self registerMaskFor: rThird) ].
	
	rTop = NoReg ifTrue:
		[ rTop := self allocateRegNotConflictingWith: topRegistersMask.
		  topRegistersMask := topRegistersMask bitOr: (self registerMaskFor: rTop) ].
	
	rNext = NoReg ifTrue:
		[ rNext := self allocateRegNotConflictingWith: topRegistersMask ].

	self deny: (rTop = NoReg or: [rNext = NoReg or: [rThird = NoReg]]).

	^ trinaryBlock value: rTop value: rNext value: rThird
]

{ #category : 'simulation stack' }
CogitAbstractStack >> allocateRegForStackTopTwoEntriesInto: binaryBlock [
	"Answers registers for the 2 top values on stack. If the values are already in registers, answers
	these registers, else allocate registers not conflicting with each others."

	| topRegistersMask rTop rNext |
	
	topRegistersMask := 0.
	rTop := rNext := NoReg.
	
	self ssTop  registerOrNone ~= NoReg ifTrue: 
		[ rTop := self ssTop registerOrNone].
	(self ssValue: 1)  registerOrNone ~= NoReg ifTrue: 
		[ topRegistersMask := self registerMaskFor: (rNext := (self ssValue: 1) registerOrNone)].
	
	rTop = NoReg ifTrue:
		[ rTop := self allocateRegNotConflictingWith: topRegistersMask ].
	
	rNext = NoReg ifTrue:
		[ rNext := self allocateRegNotConflictingWith: (self registerMaskFor: rTop) ].

	self deny: (rTop = NoReg or: [rNext = NoReg]).

	^ binaryBlock value: rTop value: rNext
]

{ #category : 'simulation stack' }
CogitAbstractStack >> allocateRegNotConflictingWith: regMask [
	| reg |
	"if there's a free register, use it"
	reg := self backEnd availableRegisterOrNoneFor: (self liveRegisters bitOr: regMask).
	reg = NoReg ifTrue: "No free register, choose one that does not conflict with regMask"
		[reg := self freeAnyRegNotConflictingWith: regMask].
	reg = ReceiverResultReg ifTrue: "If we've allocated RcvrResultReg, it's not live anymore"
		[self voidReceiverResultRegContainsSelf].
	^ reg
]

{ #category : 'simulation stack' }
CogitAbstractStack >> allocateVectorRegForStackEntryAt: index notConflictingWith: regMask [
	"If the stack entry is already in a register not conflicting with regMask, answers it,
	else allocate a new register not conflicting with reg mask"
	<var: #stackEntry type: #'CogSimStackEntry *'>
	<returnTypeC: #'signed char'>
	| stackEntry mask |
	stackEntry := self ssValue: index.
	mask := stackEntry registerMaskOrNone.
	(mask ~= 0 and: [mask noMask: regMask]) ifTrue: 
		[self flag: #TODO.
		"When one does pushDup on a SSRegister
		 followed by an operation reusing the register 
		 but mutating the value of the register, then the value that was 
		 dup is now refering to the register with a mutated value which
		 is incorrect. This problem is serious as it can happen also with 
		 multiple unsafe instructions (no dup involved)
		 This is not a problem if the operation reusing the register is not 
		 mutating the value of if all the dup values are used in the same 
		 operation.
		 => I think we should introduce allocateRegMutatingStackEntryAt:
		notConflictingWith:upThrough:, used by operations mutating the reg
		value and flushing partially the stack if somewhere between simSpill
		and the ssEntries used by the operation someone uses also the same
		register."
		 ^stackEntry registerOrNone].
	^self allocateVectorRegNotConflictingWith: regMask
]

{ #category : 'simulation stack' }
CogitAbstractStack >> allocateVectorRegNotConflictingWith: regMask [
	| reg |
	"if there's a free register, use it"
	reg := self backEnd availableVectorRegisterOrNoneFor: (self liveVectorRegisters bitOr: regMask).
	"reg = NoReg ifTrue: ""No free register, choose one that does not conflict with regMask""
		[reg := self freeAnyRegNotConflictingWith: regMask]."
	^ reg
]

{ #category : 'simulation stack' }
CogitAbstractStack >> anyReferencesToRegister: reg inAllButTopNItems: n [
	| regMask |
	regMask := self registerMaskFor: reg.
	simStackPtr - n to: 0 by: -1 do:
		[:i|
		((self simStackAt: i) registerMask anyMask: regMask) ifTrue:
			[^true]].
	^false
]

{ #category : 'simulation stack' }
CogitAbstractStack >> anyReferencesToRegister: reg inTopNItems: n [
	| regMask |
	regMask := self registerMaskFor: reg.
	simStackPtr to: simStackPtr - n + 1 by: -1 do:
		[:i|
		((self simStackAt: i) registerMask anyMask: regMask) ifTrue:
			[^true]].
	^false
]

{ #category : 'simulation stack' }
CogitAbstractStack >> availableRegOrNoneNotConflictingWith: regMask [
	"If there's a free register, answer it, otherwise answer NoReg."

	<inline: true>
	^ self backEnd availableRegisterOrNoneFor:
		  (self liveRegisters bitOr: regMask)
]

{ #category : 'accessing' }
CogitAbstractStack >> bytecodePC [

	^ cogit bytecodePC
]

{ #category : 'accessing' }
CogitAbstractStack >> cogit [
	^ cogit
]

{ #category : 'accessing' }
CogitAbstractStack >> cogit: aStackToRegisterMappingCogit [ 
	
	cogit := aStackToRegisterMappingCogit
]

{ #category : 'simulation stack' }
CogitAbstractStack >> freeAnyFloatRegNotConflictingWith: regMask [
	"Spill the closest register on stack not conflicting with regMask. 
	Assertion Failure if regMask has already all the registers"

	| reg index |
	self assert: self needsFrame.
	reg := NoReg.
	index := simSpillBase max: 0.
	self deny: reg = NoReg.
	self ssAllocateRequiredFloatReg: reg.
	^ reg
]

{ #category : 'simulation stack' }
CogitAbstractStack >> freeAnyRegNotConflictingWith: regMask [
	"Spill the closest register on stack not conflicting with regMask. 
	Assertion Failure if regMask has already all the registers"
	<var: #desc type: #'CogSimStackEntry *'>
	| reg index |
	self assert: self needsFrame.
	reg := NoReg.
	index := simSpillBase max: 0.
	[reg = NoReg and: [index < simStackPtr]] whileTrue: 
		[ | desc |
		 desc := self simStackAt: index.
		 desc type = SSRegister ifTrue:
			[(regMask anyMask: (self registerMaskFor: desc registerr)) ifFalse: 
				[reg := desc registerr]].
		 index := index + 1].
	self deny: reg = NoReg.
	self ssAllocateRequiredReg: reg.
	^reg
]

{ #category : 'simulation stack' }
CogitAbstractStack >> initialize [

	super initialize.

	simStack := CArrayAccessor on:
		            ((1 to: self simStackSlots) collect: [ :i |
			             self simStackEntryClass new cogit: self cogit ]).

	simStackPtr := 0.
	simSpillBase := simStackPtr + 1
]

{ #category : 'simulation stack' }
CogitAbstractStack >> liveFloatRegisters [
	| regsSet |
	regsSet := 0.
	(simSpillBase max: 0) to: simStackPtr do:
		[:i|
		regsSet := regsSet bitOr: (self simStackAt: i) floatRegisterMask].
	^regsSet
]

{ #category : 'simulation stack' }
CogitAbstractStack >> liveRegisters [
	| regsSet |
	self needsFrame
		ifTrue: [regsSet := 0]
		ifFalse:
			[regsSet := self registerMaskFor: ReceiverResultReg.
			 (self methodOrBlockNumArgs <= self numRegArgs
			  and: [self methodOrBlockNumArgs > 0]) ifTrue:
				[regsSet := regsSet bitOr: (self registerMaskFor: Arg0Reg).
				 (self numRegArgs > 1 and: [self methodOrBlockNumArgs > 1]) ifTrue:
					[regsSet := regsSet bitOr: (self registerMaskFor: Arg1Reg)]]].
	(simSpillBase max: 0) to: simStackPtr do:
		[:i|
		regsSet := regsSet bitOr: (self simStackAt: i) registerMask].
	^regsSet
]

{ #category : 'simulation stack' }
CogitAbstractStack >> liveVectorRegisters [

	| regsSet |
	regsSet := 0.
	(simSpillBase max: 0) to: simStackPtr do: [ :i | 
		| ssEntry |
		ssEntry := self simStackAt: i.
		(ssEntry type = SSVectorRegister) ifTrue: [ 
			regsSet := regsSet bitOr: ssEntry registerMask ] ].
	^ regsSet
]

{ #category : 'simulation stack' }
CogitAbstractStack >> marshallSendArguments: numArgs [
	"Spill everything on the simulated stack that needs spilling (that below receiver and arguments).
	 Marshall receiver and arguments to stack and/or registers depending on arg count.
	 If the args don't fit in registers push receiver and args (spill everything), but still assign
	 the receiver to ReceiverResultReg."

	self ssSpillStackExceptTop: numArgs + 1.
	numArgs > self numRegArgs
		ifTrue: [ "If there are no spills and no references to ReceiverResultReg
			 the fetch of ReceiverResultReg from the stack can be avoided
			 by assigning directly to ReceiverResultReg and pushing it."
			| numSpilled anyRefs |
			numSpilled := self numberOfSpillsInTopNItems: numArgs + 1.
			anyRefs := self anyReferencesToRegister: ReceiverResultReg inTopNItems: numArgs + 1.
			(numSpilled > 0 or: [ anyRefs ])
				ifTrue: [
					self ssSpillStack.
					(self simStackAt: simStackPtr - numArgs) copyToReg: ReceiverResultReg ]
				ifFalse: [
					(self simStackAt: simStackPtr - numArgs)
						copyToReg: ReceiverResultReg;
						type: SSRegister;
						registerr: ReceiverResultReg.
					self ssSpillStack ].
			
			"Pop from the stack, so that subsequent compilation in this unit make as if they were popped.
			However, but do not discard the entries in the runtime stack (do not generate pops).
			It's the callee responsibility of popping them."
			^ self ssPop: numArgs + 1 popSpilled: false ]
		ifFalse: [
			"Move the args to the register arguments, being careful to do
			 so last to first so e.g. previous contents don't get overwritten.
			 Also check for any arg registers in use by other args."
			numArgs > 0 ifTrue: [
				(self numRegArgs > 1 and: [ numArgs > 1 ])
					ifTrue: [
						self ssAllocateRequiredReg: Arg0Reg upThrough: simStackPtr - 2.
						self ssAllocateRequiredReg: Arg1Reg upThrough: simStackPtr - 1 ]
					ifFalse: [ self ssAllocateRequiredReg: Arg0Reg upThrough: simStackPtr - 1 ] ].

			(self numRegArgs > 1 and: [ numArgs > 1 ]) ifTrue: [ (self simStackAt: simStackPtr) copyToReg: Arg1Reg ].

			numArgs > 0 ifTrue: [ (self simStackAt: simStackPtr - numArgs + 1) copyToReg: Arg0Reg ].
			(self simStackAt: simStackPtr - numArgs) copyToReg: ReceiverResultReg.

			"Pop from the stack, so that subsequent compilation in this unit make as if they were popped.
			Here, DO discard the entries in the runtime stack.
			The calling convention dictates that in this case all receiver/args pass through registers and no stack is involved.
			If we don't pop from the runtime stack, it will get desynchronised"
			self ssPop: numArgs + 1 ]
]

{ #category : 'accessing' }
CogitAbstractStack >> methodOrBlockNumTemps [

	^ cogit methodOrBlockNumTemps
]

{ #category : 'testing' }
CogitAbstractStack >> needsFrame [
	
	^ cogit needsFrame
]

{ #category : 'simulation stack' }
CogitAbstractStack >> numberOfSpillsInTopNItems: n [
	simStackPtr to: simStackPtr - n + 1 by: -1 do:
		[:i| (self simStackAt: i) type = SSSpill ifTrue:
			[^n - (simStackPtr - i)]].
	^0
]

{ #category : 'simulation stack' }
CogitAbstractStack >> simStackAt: index [
	<cmacro: '(index) (simStack + (index))'>
	<returnTypeC: #'CogSimStackEntry *'>
	^self addressOf: (simStack at: index)
]

{ #category : 'simulation stack' }
CogitAbstractStack >> simStackEntryClass [
	<doNotGenerate>
	^CogSimStackEntry
]

{ #category : 'simulation stack' }
CogitAbstractStack >> simStackSlots [
	"Answer the number of slots to include in a simulated stack.
	 This needs to be big enough to include all stack slots in a context
	 plus a slot for the receiver and some overflow for safety."
	<inline: true>
	^((LargeContextSlots - CtxtTempFrameStart + 1 max: 64) * 11 // 10)
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateCallReg: requiredReg [
	"Allocate a register needed in a run-time call (i.e. flush uses of the
	 register to the real stack).  Since the run-time can smash any and
	 all caller-saved registers also flush all caller-saved registers."
	<inline: true>
	self ssAllocateRequiredRegMask: (CallerSavedRegisterMask
										bitOr: (self registerMaskFor: requiredReg))
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateCallReg: requiredReg1 and: requiredReg2 [
	"Allocate registers needed in a run-time call (i.e. flush uses of the
	 registers to the real stack).  Since the run-time can smash any and
	 all caller-saved registers also flush all caller-saved registers."
	<inline: true>
	self ssAllocateRequiredRegMask: (CallerSavedRegisterMask
										bitOr: ((self registerMaskFor: requiredReg1)
										bitOr: (self registerMaskFor: requiredReg2)))
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateCallReg: requiredReg1 and: requiredReg2 and: requiredReg3 [
	"Allocate registers needed in a run-time call (i.e. flush uses of the
	 registers to the real stack).  Since the run-time can smash any and
	 all caller-saved registers also flush all caller-saved registers."
	<inline: true>
	self ssAllocateRequiredRegMask: (CallerSavedRegisterMask bitOr:
										(self registerMaskFor: requiredReg1 and: requiredReg2 and: requiredReg3))
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateCallReg: requiredReg1 and: requiredReg2 and: requiredReg3 and: requiredReg4 [
	"Allocate registers needed in a run-time call (i.e. flush uses of the
	 registers to the real stack).  Since the run-time can smash any and
	 all caller-saved registers also flush all caller-saved registers."
	<inline: true>
	self ssAllocateRequiredRegMask: (CallerSavedRegisterMask
										bitOr: ((self registerMaskFor: requiredReg1)
										bitOr: ((self registerMaskFor: requiredReg2)
										bitOr: ((self registerMaskFor: requiredReg3)
										bitOr: (self registerMaskFor: requiredReg4)))))
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateCallReg: requiredReg1 and: requiredReg2 upThrough: aStackPointer [
	"Allocate registers needed in a run-time call (i.e. flush uses of the
	 registers to the real stack).  Since the run-time can smash any and
	 all caller-saved registers also flush all caller-saved registers."
	<inline: true>
	self ssAllocateRequiredRegMask: (CallerSavedRegisterMask
										bitOr: ((self registerMaskFor: requiredReg1)
										bitOr: (self registerMaskFor: requiredReg2)))
		upThrough: aStackPointer
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateCallReg: requiredReg upThrough: aStackPointer [
	"Allocate a register needed in a run-time call (i.e. flush uses of the
	 register to the real stack).  Since the run-time can smash any and
	 all caller-saved registers also flush all caller-saved registers."
	<inline: true>
	self ssAllocateRequiredRegMask: (CallerSavedRegisterMask
										bitOr: (self registerMaskFor: requiredReg))
		upThrough: aStackPointer
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredFloatReg: requiredReg [
	self ssAllocateRequiredFloatRegMask: (self registerMaskFor: requiredReg)
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredFloatRegMask: requiredRegsMask upThrough: stackPtr [
	| lastRequired lastRequiredNative liveRegs |
	lastRequired := -1.
	lastRequiredNative := -1.
	"compute live regs while noting the last occurrence of required regs.
	 If these are not free we must spill from simSpillBase to last occurrence.
	 Note we are conservative here; we could allocate FPReg in frameless methods."
	liveRegs := NoReg.
	(simSpillBase max: 0) to: stackPtr do:
		[:i|
		liveRegs := liveRegs bitOr: (self simStackAt: i) registerMask.
		((self simStackAt: i) floatRegisterMask bitAnd: requiredRegsMask) ~= 0 ifTrue:
			[lastRequired := i]].

	"If any of requiredRegsMask are live we must spill."
	(liveRegs bitAnd: requiredRegsMask) = 0 ifFalse:
		["Some live, must spill"
		self ssFlushTo: lastRequired.
		self assert: (self liveFloatRegisters bitAnd: requiredRegsMask) = 0]
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredReg: requiredReg [
	<inline: true>
	self ssAllocateRequiredRegMask: (self registerMaskFor: requiredReg)
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredReg: requiredReg1 and: requiredReg2 [
	<inline: true>
	self ssAllocateRequiredRegMask: ((self registerMaskFor: requiredReg1)
										bitOr: (self registerMaskFor: requiredReg2))
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredReg: requiredReg1 and: requiredReg2 upThrough: stackPointer [
	<inline: true>
	self ssAllocateRequiredRegMask: ((self registerMaskFor: requiredReg1)
										bitOr: (self registerMaskFor: requiredReg2))
		upThrough: stackPointer
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredReg: requiredReg upThrough: stackPtr [
	<inline: true>
	self ssAllocateRequiredRegMask: (self registerMaskFor: requiredReg)
		upThrough: stackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredRegMask: requiredRegsMask upThrough: stackPtr [
	| lastRequired lastRequiredNative liveRegs |
	lastRequired := -1.
	lastRequiredNative := -1.
	"compute live regs while noting the last occurrence of required regs.
	 If these are not free we must spill from simSpillBase to last occurrence.
	 Note we are conservative here; we could allocate FPReg in frameless methods."
	liveRegs := self registerMaskFor: FPReg and: SPReg.
	(simSpillBase max: 0) to: stackPtr do:
		[:i|
		liveRegs := liveRegs bitOr: (self simStackAt: i) registerMask.
		((self simStackAt: i) registerMask anyMask: requiredRegsMask) ifTrue:
			[lastRequired := i]].
	"If any of requiredRegsMask are live we must spill."
	(liveRegs anyMask: requiredRegsMask) ifTrue:
		[self ssFlushTo: lastRequired.
		 self deny: (self liveRegisters anyMask: requiredRegsMask)]
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssFlushTo: index [

	<inline: true>
	self assert: self tempsValidAndVolatileEntriesSpilled.
	simSpillBase <= index ifTrue: [
		(((simSpillBase max: self methodOrBlockNumTemps + 1) min: simStackPtr)
			 min: index) to: index do: [ :i |
			self assert: self needsFrame.
			self ssSpillEntryAt: i ].
		simSpillBase := index + 1 ]
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssFlushUpThrough: unaryBlock [
	"Any occurrences on the stack of the value being stored (which is the top of stack)
	 must be flushed, and hence any values colder than them stack."

	self assert: simSpillBase >= 0.
	simStackPtr - 1 to: simSpillBase by: -1 do:
		[ :index |
		(unaryBlock value: (self simStackAt: index)) ifTrue: [ ^ self ssFlushTo: index ] ]
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssFlushUpThroughReceiverVariable: slotIndex [
	"Any occurrences on the stack of the value being stored (which is the top of stack)
	 must be flushed, and hence any values colder than them stack."
	<var: #desc type: #'CogSimStackEntry *'>
	self ssFlushUpThrough: 
		[ :desc |  
			desc type = SSBaseOffset
			 and: [desc registerr = ReceiverResultReg
			 and: [desc offset = (objectRepresentation slotOffsetOfInstVarIndex: slotIndex) ] ] ]
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssFlushUpThroughRegister: reg [
	"Any occurrences on the stack of the register must be
	 flushed, and hence any values colder than them stack."
	<var: #desc type: #'CogSimStackEntry *'>
	self ssFlushUpThrough: [ :desc | desc type = SSRegister and: [ desc registerr = reg ] ]
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssFlushUpThroughTemporaryVariable: tempIndex [
	"Any occurrences on the stack of the value being stored (which is the top of stack)
	 must be flushed, and hence any values colder than them stack."
	<var: #desc type: #'CogSimStackEntry *'>
	| offset |
	offset := (self simStackAt: tempIndex + 1) offset.
	self assert: offset = (self frameOffsetOfTemporary: tempIndex).
	self ssFlushUpThrough: 
		[ :desc |
			desc type = SSBaseOffset
		 	and: [desc registerr = FPReg
		 	and: [desc offset = offset ] ] ]
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPop: n [
	
	self ssPop: n popSpilled: true
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPop: popBoolean andCopyReg: reg [
	"Store or pop the top simulated stack entry to a register.
	N.B.: popToReg: and storeToReg: does not generate anything if 
	it moves a register to the same register."

	popBoolean
		ifTrue: [ self ssPopTopToReg: reg ]
		ifFalse: [ self ssTop copyToReg: reg ]
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPop: n popSpilled: popSpilled [
	| spilledToPop |
	self assert: (simStackPtr - n >= self methodOrBlockNumTemps
				or: [(self needsFrame not and: [simStackPtr - n >= 0])]).

	"Pop from the simulated stack"
	simStackPtr := simStackPtr - n.

	"Check how many elements to pop from the stack have been spilled.
	If the spill base is above the stack, it means we popped spilled elements.
	If the spill base is below or equals to the stack pointer, we don't need ot do anything"	
	spilledToPop := simSpillBase - 1 - simStackPtr.
	(popSpilled and: [spilledToPop > 0]) ifTrue:
		[self cogit AddCq: spilledToPop * self wordSize R: SPReg].
	
	self updateSimSpillBase
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPush: n [ 
	simStackPtr := simStackPtr + n
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPushAnnotatedConstant: literal [
	self ssPushConstant: literal.
	self annotateInstructionForBytecode.
	^0
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPushBase: reg offset: offset [
	self ssPush: 1.
	self ssTop
		type: SSBaseOffset;
		spilled: false;
		registerr: reg;
		offset: offset;
		bcptr: self bytecodePC.
	self updateSimSpillBase.
	^0
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPushConstant: literal [
	self ssPush: 1.
	self ssTop
		type: SSConstant;
		spilled: false;
		constant: literal;
		bcptr: self bytecodePC.
	self updateSimSpillBase.
	^0
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPushDesc: simStackEntry [
	<var: #simStackEntry type: #SimStackEntry>
	self cCode:
			[simStackEntry type = SSSpill ifTrue:
				[simStackEntry type: SSBaseOffset].
			simStackEntry
				spilled: false;
				bcptr: self bytecodePC.
			 simStack
				at: (simStackPtr := simStackPtr + 1)
				put: simStackEntry]
		inSmalltalk:
			[(simStack at: (simStackPtr := simStackPtr + 1))
				copyFrom: simStackEntry;
				type: (simStackEntry type = SSSpill
						ifTrue: [SSBaseOffset]
						ifFalse: [simStackEntry type]);
				spilled: false;
				bcptr: self bytecodePC].
	self updateSimSpillBase.
	^0
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPushRegister: reg [
	self ssPush: 1.
	self ssTop
		type: SSRegister;
		spilled: false;
		registerr: reg;
		bcptr: self bytecodePC.
	self updateSimSpillBase.
	^0
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPushVectorRegister: reg [
	self ssPush: 1.
	self ssTop
		type: SSVectorRegister;
		spilled: false;
		registerr: reg;
		bcptr: self bytecodePC.
	self ssTop.
	self updateSimSpillBase.
	^0
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssSelfDescriptor [
	<returnTypeC: #SimStackEntry>
	<inline: true>
	^simStack at: 0
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssSize [
	
	^ simStackPtr + 1
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssSpillEntryAt: i [

	<inline: true>
	self assert: self needsFrame.
	"frameOffsetOfTemporary: is 0-relative"
	(self simStackAt: i)
		ensureSpilledAt: (self cogit frameOffsetOfTemporary: i - 1)
		from: FPReg
]

{ #category : 'as yet unclassified' }
CogitAbstractStack >> ssSpillStack [
	
	self ssSpillStackExceptTop: 0
]

{ #category : 'as yet unclassified' }
CogitAbstractStack >> ssSpillStackExceptTop: n [
	
	self ssFlushTo: simStackPtr - n
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssStoreAndReplacePop: popBoolean toReg: reg [
	"In addition to ssStorePop:toReg:, if this is a store and not
	a popInto I change the simulated stack to use the register 
	for the top value"
	| topSpilled |
	topSpilled := self ssTop spilled.
	self ssPop: (popBoolean or: [topSpilled]) andCopyReg: reg.
	popBoolean ifFalse: 
		[ topSpilled ifFalse: [self ssPop: 1 popSpilled: false ].
		self ssPushRegister: reg ].
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssStorePop: popBoolean toPreferredReg: preferredReg [
	"Store or pop the top simulated stack entry to a register.
	 Use preferredReg if the entry is not itself a register.
	 Answer the actual register the result ends up in."
	| actualReg |
	actualReg := preferredReg.
	self ssTop type = SSRegister ifTrue: 
		[self assert: self ssTop spilled not.
		 actualReg := self ssTop registerr].
	self ssPop: popBoolean andCopyReg: actualReg. "generates nothing if ssTop is already in actualReg"
	^ actualReg
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssTop [
	<returnTypeC: #'CogSimStackEntry *'>
	^self simStackAt: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssTopDescriptor [
	<returnTypeC: #SimStackEntry>
	<inline: true>
	^simStack at: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssValue: n [
	<returnTypeC: #'CogSimStackEntry *'>
	^self simStackAt: simStackPtr - n
]

{ #category : 'validation' }
CogitAbstractStack >> tempsValidAndVolatileEntriesSpilled [
	"Answer if the stack is valid up to, but not including, simSpillBase."
	| culprit |
	1 to: self methodOrBlockNumTemps do:
		[:i|
		 ((self simStackAt: i) type = SSBaseOffset) ifFalse:
			[culprit ifNil: [culprit := i].
			 ^false]].
	self methodOrBlockNumTemps + 1 to: simSpillBase - 1 do:
		[:i|
		 (self simStackAt: i) spilled ifFalse:
			[culprit ifNil: [culprit := i].
			 ^false]].
	^true
]

{ #category : 'simulation stack' }
CogitAbstractStack >> updateSimSpillBase [
	"Something volatile has been pushed on the stack; update simSpillBase accordingly."
	<inline: true>
	self assert: ((simSpillBase > self methodOrBlockNumTemps
				and: [simStackPtr >= self methodOrBlockNumTemps])).
	simSpillBase > simStackPtr
		ifTrue:
			[simSpillBase := simStackPtr + 1.
			 [simSpillBase - 1 > self methodOrBlockNumTemps
			   and: [(self simStackAt: simSpillBase - 1) spilled not]] whileTrue:
				[simSpillBase := simSpillBase - 1]]
		ifFalse:
			[[(self simStackAt: simSpillBase) spilled
			   and: [simSpillBase <= simStackPtr]] whileTrue:
				[simSpillBase := simSpillBase + 1]].
	self methodOrBlockNumTemps + 1 to: (simSpillBase - 1 min: simStackPtr) do:
		[:i|
		self assert: (self simStackAt: i) spilled == true].
	self assert: (simSpillBase > simStackPtr or: [(self simStackAt: simSpillBase) spilled == false])
]

{ #category : 'accessing' }
CogitAbstractStack >> wordSize [

	^ cogit objectMemory wordSize
]

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
		'VMBytecodeConstants',
		'VMStackFrameOffsets'
	],
	#category : 'VMMaker-JIT',
	#package : 'VMMaker',
	#tag : 'JIT'
}

{ #category : 'translation' }
CogitAbstractStack class >> instVarNamesAndTypesForTranslationDo: aBinaryBlock [
	"Enumerate aBinaryBlock with the names and C type strings for the inst vars to include in an AbstractInstruction struct."

	self filteredInstVarNames do: [ :ivn |
		aBinaryBlock value: ivn value: (ivn caseOf: {
					 ([ 'simStackPtr' ] -> [ #sqInt ]).
					 ([ 'simSpillBase' ] -> [ #sqInt ]).
					 ([ 'simStack' ] -> [ #'sqInt *' ]) }) ]
]

{ #category : 'bytecode generator support' }
CogitAbstractStack >> allocateEqualsEqualsRegistersArgNeedsReg: argNeedsReg rcvrNeedsReg: rcvrNeedsReg into: binaryBlock [

	| argReg rcvrReg |
	self assert: (argNeedsReg or: [ rcvrNeedsReg ]).
	argReg := rcvrReg := NoReg.
	argNeedsReg
		ifTrue: [
			rcvrNeedsReg
				ifTrue: [
					self allocateRegForStackTopTwoEntriesInto: [ :rTop :rNext |
						argReg := rTop.
						rcvrReg := rNext ].
					self ssTop copyToReg: argReg.
					(self ssValue: 1) copyToReg: rcvrReg ]
				ifFalse: [
					argReg := self allocateRegForStackEntryAt: 0.
					self ssTop copyToReg: argReg ] ]
		ifFalse: [
			self assert: rcvrNeedsReg.
			self deny: self ssTop spilled.
			rcvrReg := self allocateRegForStackEntryAt: 1.
			(self ssValue: 1) copyToReg: rcvrReg ].

	self deny: (argNeedsReg and: [ argReg = NoReg ]).
	self deny: (rcvrNeedsReg and: [ rcvrReg = NoReg ]).

	binaryBlock value: rcvrReg value: argReg
]

{ #category : 'simulation stack' }
CogitAbstractStack >> allocateFloatRegNotConflictingWith: regMask [
	| reg |
	"if there's a free register, use it"
	reg := cogit backEnd availableFloatRegisterOrNoneFor: (self liveFloatRegisters bitOr: regMask).
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
		[ rNext := self allocateRegNotConflictingWith: (cogit registerMaskFor: rTop) ].

	self deny: (rTop = NoReg or: [rNext = NoReg]).

	^ binaryBlock value: rTop value: rNext
]

{ #category : 'simulation stack' }
CogitAbstractStack >> allocateRegNotConflictingWith: regMask [
	| reg |
	"if there's a free register, use it"
	reg := cogit backEnd availableRegisterOrNoneFor: (self liveRegisters bitOr: regMask).
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
	<inline: true>
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
	reg := cogit backEnd availableVectorRegisterOrNoneFor: (self liveVectorRegisters bitOr: regMask).
	"reg = NoReg ifTrue: ""No free register, choose one that does not conflict with regMask""
		[reg := self freeAnyRegNotConflictingWith: regMask]."
	^ reg
]

{ #category : 'simulation stack' }
CogitAbstractStack >> anyReferencesToRegister: reg inTopNItems: n [
	| regMask |
	regMask := cogit registerMaskFor: reg.
	simStackPtr to: simStackPtr - n + 1 by: -1 do:
		[:i|
		((self simStackAt: i) registerMask anyMask: regMask) ifTrue:
			[^true]].
	^false
]

{ #category : 'compile abstract instructions' }
CogitAbstractStack >> assertCorrectSimStackPtr [
	<inline: true>
	"Would like to assert simply simSpillBase > methodOrBlockNumTemps but can't because
	 of the initialNils hack for nested blocks in SqueakV3PlusClosures"
	self assert: (simSpillBase >= cogit getMethodOrBlockNumTemps).
	(self needsFrame and: [simSpillBase > 0]) ifTrue:
		[self assert: (self simStackAt: simSpillBase - 1) spilled == true.
		 self assert: (simSpillBase > simStackPtr or: [(self simStackAt: simSpillBase) spilled == false])].
 	self cCode: '' inSmalltalk:
		[cogit deadCode ifFalse:
			[self assert: simStackPtr + (self needsFrame ifTrue: [0] ifFalse: [1])
						= (cogit debugStackPointerFor: self bytecodePC)]].
]

{ #category : 'simulation stack' }
CogitAbstractStack >> availableRegOrNoneNotConflictingWith: regMask [
	"If there's a free register, answer it, otherwise answer NoReg."

	<inline: true>
	^ cogit backEnd availableRegisterOrNoneFor:
		  (self liveRegisters bitOr: regMask)
]

{ #category : 'accessing' }
CogitAbstractStack >> bytecodePC [

	<doNotGenerate>
	^ cogit bytecodePC
]

{ #category : 'accessing' }
CogitAbstractStack >> cogit [

	<doNotGenerate>
	^ cogit
]

{ #category : 'accessing' }
CogitAbstractStack >> cogit: aStackToRegisterMappingCogit [

	<doNotGenerate>
	cogit := aStackToRegisterMappingCogit
]

{ #category : 'copying' }
CogitAbstractStack >> copySelfTo: aRegister [

	<inline: true>
	self simSelf copyToReg: aRegister
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
			[(regMask anyMask: (cogit registerMaskFor: desc registerr)) ifFalse: 
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
CogitAbstractStack >> isLiveRegister: aRegister [

	^ self liveRegisters anyMask: (cogit registerMaskFor: aRegister)
]

{ #category : 'simulation stack' }
CogitAbstractStack >> liveEntryForRegister: aRegister above: anEntry [
	"Return the entry using the live register or 0 if the register is not live (thus no entry)"

	<returnTypeC: #'CogSimStackEntry *'>
	| aboveIndex |
	aboveIndex := self ssSize - (simStack object indexOf: anEntry).
	(simSpillBase max: 0) to: simStackPtr - aboveIndex - 1 do: [ :i |
		| maybeLiveEntry |
		maybeLiveEntry := self simStackAt: i.
		maybeLiveEntry usedRegister = aRegister ifTrue: [ ^ maybeLiveEntry ] ].
	^ 0
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
			[regsSet := cogit registerMaskFor: ReceiverResultReg.
			 (cogit methodOrBlockNumArgs <= cogit numRegArgs
			  and: [cogit methodOrBlockNumArgs > 0]) ifTrue:
				[regsSet := regsSet bitOr: (cogit registerMaskFor: Arg0Reg).
				 (cogit numRegArgs > 1 and: [cogit methodOrBlockNumArgs > 1]) ifTrue:
					[regsSet := regsSet bitOr: (cogit registerMaskFor: Arg1Reg)]]].
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

{ #category : 'testing' }
CogitAbstractStack >> needsFrame [

	<doNotGenerate>
	^ cogit needsFrame
]

{ #category : 'abstract stack' }
CogitAbstractStack >> newFreshRegister [

	^ self availableRegOrNoneNotConflictingWith: self liveRegisters
]

{ #category : 'simulation stack' }
CogitAbstractStack >> numberOfSpillsInTopNItems: n [
	simStackPtr to: simStackPtr - n + 1 by: -1 do:
		[:i| (self simStackAt: i) type = SSSpill ifTrue:
			[^n - (simStackPtr - i)]].
	^0
]

{ #category : 'copying' }
CogitAbstractStack >> postCopy [

	super postCopy.
	simStack := CArrayAccessor on: (simStack object collect: [ :e | e copy ])
]

{ #category : 'abstract stack' }
CogitAbstractStack >> restoreSimStackAtMergePoint: fixup [
	<inline: true>
	"All the execution paths reaching a merge point expect everything
	 to be spilled on stack. Throw away all simStack optimization state."
	self voidReceiverOptStatus.
	cogit getMethodOrBlockNumTemps + 1 to: simStackPtr do:
		[:i|
		 (self simStackAt: i)
			type: SSSpill;
			offset: FoxMFReceiver - (i - cogit methodOrBlockNumArgs * cogit objectMemory bytesPerOop);
			registerr: FPReg;
			spilled: true].
	simSpillBase := simStackPtr + 1.
	^ 0
]

{ #category : 'accessing' }
CogitAbstractStack >> simSelf [
	<cmacro: '() simStack'>
	<returnTypeC: #'CogSimStackEntry *'>
	<inline: true>
	^self simStackAt: 0
]

{ #category : 'simulation stack' }
CogitAbstractStack >> simSelfLiveRegister: aRegister [

	self simSelf liveRegister: aRegister
]

{ #category : 'accessing' }
CogitAbstractStack >> simSpillBase [

	^ simSpillBase
]

{ #category : 'accessing' }
CogitAbstractStack >> simSpillBase: anInteger [ 
	simSpillBase := anInteger
]

{ #category : 'simulation stack' }
CogitAbstractStack >> simStackAt: index [
	<cmacro: '(index) (simStack + (index))'>
	<returnTypeC: #'CogSimStackEntry *'>
	^self addressOf: (simStack at: index)
]

{ #category : 'simulation stack' }
CogitAbstractStack >> simStackDescriptorAt: index [
	"Return a copy of the given descriptor"
	<returnTypeC: #'CogSimStackEntry'>
	^ simStack at: index
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
										bitOr: (cogit registerMaskFor: requiredReg))
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateCallReg: requiredReg1 and: requiredReg2 [
	"Allocate registers needed in a run-time call (i.e. flush uses of the
	 registers to the real stack).  Since the run-time can smash any and
	 all caller-saved registers also flush all caller-saved registers."
	<inline: true>
	self ssAllocateRequiredRegMask: (CallerSavedRegisterMask
										bitOr: ((cogit registerMaskFor: requiredReg1)
										bitOr: (cogit registerMaskFor: requiredReg2)))
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateCallReg: requiredReg1 and: requiredReg2 and: requiredReg3 [
	"Allocate registers needed in a run-time call (i.e. flush uses of the
	 registers to the real stack).  Since the run-time can smash any and
	 all caller-saved registers also flush all caller-saved registers."
	<inline: true>
	self ssAllocateRequiredRegMask: (CallerSavedRegisterMask bitOr:
										(cogit registerMaskFor: requiredReg1 and: requiredReg2 and: requiredReg3))
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateCallReg: requiredReg1 and: requiredReg2 and: requiredReg3 and: requiredReg4 [
	"Allocate registers needed in a run-time call (i.e. flush uses of the
	 registers to the real stack).  Since the run-time can smash any and
	 all caller-saved registers also flush all caller-saved registers."
	<inline: true>
	self ssAllocateRequiredRegMask: (CallerSavedRegisterMask
										bitOr: ((cogit registerMaskFor: requiredReg1)
										bitOr: ((cogit registerMaskFor: requiredReg2)
										bitOr: ((cogit registerMaskFor: requiredReg3)
										bitOr: (cogit registerMaskFor: requiredReg4)))))
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

{ #category : 'abstract stack' }
CogitAbstractStack >> ssAllocateRegisters [

	^ self ssAllocateRegistersForceSpilling: false
]

{ #category : 'abstract stack' }
CogitAbstractStack >> ssAllocateRegistersForceSpilling: forceSpilling [
	"Iterate the stack from top to bottom.
	For each entry, if it is:
		- constant: allocate a register, move the constant to that register, update the stack
		- register: do nothing, we already have a register
		- memory address: do nothing for now, it's spilled.

	If during register allocation we run out of registers, or we force spilling, spill the slot instead:
		- push the value to memory
		- update the stack with the spill address.
	
	Forced spilling is useful for testing"

	"Iterate only the entries between the stack top and the spill base.
	This way we only iterate non spilled entries"

	| shouldContinueAllocation hottestIndexToSpill |
	"First iterate all entries from top to bottom until we run out of registers.
	When we run out of registers, store into hottestIndexToSpill the index of the new spilling base.
	"
	shouldContinueAllocation := true.
	hottestIndexToSpill := simSpillBase - 1.
	simStackPtr to: simSpillBase by: -1 do: [ :index |
		| stackEntry |
		stackEntry := self simStackAt: index.
		shouldContinueAllocation ifTrue: [
			stackEntry type = SSConstant ifTrue: [
				| freshRegister |
				freshRegister := self allocateRegNotConflictingWith: 0.
				shouldContinueAllocation := freshRegister ~= NoReg and: [
					                            forceSpilling not ].

				shouldContinueAllocation ifFalse: [ hottestIndexToSpill := index ].
				shouldContinueAllocation ifTrue: [
					cogit MoveCq: stackEntry constant R: freshRegister.
					stackEntry type: SSRegister.
					stackEntry spilled: false.
					stackEntry registerr: freshRegister ] ] ] ].

	"Now spill everything in between the old spill base and the new spill base"
	self ssFlushTo: hottestIndexToSpill
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredFloatReg: requiredReg [
	self ssAllocateRequiredFloatRegMask: (cogit registerMaskFor: requiredReg)
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
	self ssAllocateRequiredRegMask: (cogit registerMaskFor: requiredReg)
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredReg: requiredReg1 and: requiredReg2 [
	<inline: true>
	self ssAllocateRequiredRegMask: ((cogit registerMaskFor: requiredReg1)
										bitOr: (cogit registerMaskFor: requiredReg2))
		upThrough: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredReg: requiredReg1 and: requiredReg2 upThrough: stackPointer [
	<inline: true>
	self ssAllocateRequiredRegMask: ((cogit registerMaskFor: requiredReg1)
										bitOr: (cogit registerMaskFor: requiredReg2))
		upThrough: stackPointer
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredReg: requiredReg upThrough: stackPtr [
	<inline: true>
	self ssAllocateRequiredRegMask: (cogit registerMaskFor: requiredReg)
		upThrough: stackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssAllocateRequiredRegMask: requiredRegsMask upThrough: stackPtr [
	<inline: true>
	| lastRequired lastRequiredNative liveRegs |
	lastRequired := -1.
	lastRequiredNative := -1.
	"compute live regs while noting the last occurrence of required regs.
	 If these are not free we must spill from simSpillBase to last occurrence.
	 Note we are conservative here; we could allocate FPReg in frameless methods."
	liveRegs := cogit registerMaskFor: FPReg and: SPReg.
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
		(((simSpillBase max: cogit getMethodOrBlockNumTemps + 1) min:
			  simStackPtr) min: index) to: index do: [ :i |
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
			 and: [desc offset = (cogit objectRepresentation slotOffsetOfInstVarIndex: slotIndex) ] ] ]
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
	self assert: offset = (cogit frameOffsetOfTemporary: tempIndex).
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
	self assert: (simStackPtr - n >= cogit getMethodOrBlockNumTemps
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

{ #category : 'mapped inline primitive generators - vectorial' }
CogitAbstractStack >> ssPopTopToReg: aRegister [
	
	"Peephole optimisation: generate always a single instruction.
	If the top is spilled, generate just a pop instruction. Otherwise a copy/load"
	self ssTop spilled
		ifTrue: [ cogit PopR: aRegister ]
		ifFalse: [ self ssTop copyToReg: aRegister ].
	"No need to spill from the physical stack, we already did it"
	self ssPop: 1 popSpilled: false.
]

{ #category : 'mapped inline primitive generators - vectorial' }
CogitAbstractStack >> ssPopTopToVectorReg: aVectorRegister [

	<inline: true>
	self ssTop moveToVectorReg: aVectorRegister.
	self ssPop: 1
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPush: n [ 
	simStackPtr := simStackPtr + n
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssPushAnnotatedConstant: literal [
	self ssPushConstant: literal.
	cogit annotateInstructionForBytecode.
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
	<inline: true>
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
	<inline: true>
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
	<inline: true>
	<returnTypeC: #'CogSimStackEntry *'>
	^self simStackAt: simStackPtr
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssTopDescriptor [
	<returnTypeC: #SimStackEntry>
	<inline: true>
	^simStack at: simStackPtr
]

{ #category : 'testing' }
CogitAbstractStack >> ssTopNeedsStoreCheck [
	<inline: true>
	^self ssTop type ~= SSConstant
	  or: [(cogit objectMemory isNonImmediate: self ssTop constant)
		and: [cogit objectRepresentation shouldAnnotateObjectReference:  self ssTop constant]]
]

{ #category : 'simulation stack' }
CogitAbstractStack >> ssValue: n [
	<returnTypeC: #'CogSimStackEntry *'>
	^self simStackAt: simStackPtr - n
]

{ #category : 'testing' }
CogitAbstractStack >> stackEntryIsBoolean: simStackEntry [
	<var: #simStackEntry type: #'CogSimStackEntry *'>
	<inline: true>
	^simStackEntry type = SSConstant
	  and: [simStackEntry constant = cogit objectMemory trueObject
			or: [simStackEntry constant = cogit objectMemory falseObject]]
]

{ #category : 'testing' }
CogitAbstractStack >> stackTopIsBoolean [
	<inline: true>
	^simStackPtr >= cogit methodOrBlockNumArgs and: [self stackEntryIsBoolean: self ssTop]
]

{ #category : 'validation' }
CogitAbstractStack >> tempsValidAndVolatileEntriesSpilled [
	"Answer if the stack is valid up to, but not including, simSpillBase."
	| culprit |
	1 to: cogit getMethodOrBlockNumTemps do:
		[:i|
		 ((self simStackAt: i) type = SSBaseOffset) ifFalse:
			[culprit ifNil: [culprit := i].
			 ^false]].
	cogit getMethodOrBlockNumTemps + 1 to: simSpillBase - 1 do:
		[:i|
		 (self simStackAt: i) spilled ifFalse:
			[culprit ifNil: [culprit := i].
			 ^false]].
	^true
]

{ #category : 'accessing' }
CogitAbstractStack >> theSimStackPtr [

	^ simStackPtr
]

{ #category : 'accessing' }
CogitAbstractStack >> theSimStackPtr: anInteger [

	simStackPtr := anInteger
]

{ #category : 'simulation stack' }
CogitAbstractStack >> updateSimSpillBase [
	"Something volatile has been pushed on the stack; update simSpillBase accordingly."
	<inline: true>
	self assert: ((simSpillBase > cogit getMethodOrBlockNumTemps
				and: [simStackPtr >= cogit getMethodOrBlockNumTemps])).
	simSpillBase > simStackPtr
		ifTrue:
			[simSpillBase := simStackPtr + 1.
			 [simSpillBase - 1 > cogit getMethodOrBlockNumTemps
			   and: [(self simStackAt: simSpillBase - 1) spilled not]] whileTrue:
				[simSpillBase := simSpillBase - 1]]
		ifFalse:
			[[(self simStackAt: simSpillBase) spilled
			   and: [simSpillBase <= simStackPtr]] whileTrue:
				[simSpillBase := simSpillBase + 1]].
	cogit getMethodOrBlockNumTemps + 1 to: (simSpillBase - 1 min: simStackPtr) do:
		[:i|
		self assert: (self simStackAt: i) spilled == true].
	self assert: (simSpillBase > simStackPtr or: [(self simStackAt: simSpillBase) spilled == false])
]

{ #category : 'abstract stack' }
CogitAbstractStack >> voidReceiverOptStatus [
	"Used to mark ReceiverResultReg as dead or not containing simSelf.
	 Used when the simStack has already been flushed, e.g. for sends."
	<inline: true>
	self simSelf liveRegister: NoReg
]

{ #category : 'bytecode generator support' }
CogitAbstractStack >> voidReceiverResultRegContainsSelf [
	"Used when ReceiverResultReg is allocated for other than simSelf, and
	 there may be references to ReceiverResultReg which need to be spilled."
	| spillIndex |
	self voidReceiverOptStatus.
	spillIndex := 0.
	(cogit getMethodOrBlockNumTemps + 1 max: simSpillBase) to: simStackPtr do:
		[:i|
		(self simStackAt: i) registerOrNone = ReceiverResultReg ifTrue:
			[spillIndex := i]].
	spillIndex > 0 ifTrue:
		[self ssFlushTo: spillIndex]
]

{ #category : 'accessing' }
CogitAbstractStack >> wordSize [

	<doNotGenerate>
	^ cogit objectMemory wordSize
]

control primitives
activateNewClosureMethod: blockClosure numArgs: numArgs mayContextSwitch: mayContextSwitch
	"Similar to activateNewMethod but for Closure and newMethod.
	 Override to handle the various interpreter/machine code transitions
	 and to create an appropriate frame layout."
	| numCopied outerContext theMethod methodHeader inInterpreter closureIP switched |
	<inline: true>
	outerContext := objectMemory fetchPointer: ClosureOuterContextIndex ofObject: blockClosure.
	self assert: (objectMemory isContext: outerContext).
	self assert: outerContext ~= blockClosure.
	numCopied := self copiedValueCountOfClosure: blockClosure.
	theMethod := objectMemory fetchPointer: MethodIndex ofObject: outerContext.
	self assert: (objectMemory isOopCompiledMethod: theMethod).
	methodHeader := self rawHeaderOf: theMethod.
	(self isCogMethodReference: methodHeader) ifTrue:
		[^self executeCogBlock: (self cogMethodOf: theMethod)
			closure: blockClosure
			mayContextSwitch: mayContextSwitch].
	"How do we know when to compile a block method?
	 One simple criterion is to check if the block is running within its inner context,
	 i.e. if the outerContext is married.
	 Even simpler is to remember the previous block entered via the interpreter and
	 compile if this is the same one.  But we can thrash trying to compile an uncoggable
	 method unless we try and remember which ones can't be cogged.  So also record
	 the last block method we failed to compile and avoid recompiling it."
	(self methodWithHeaderShouldBeCogged: methodHeader)
		ifTrue:
			[theMethod = lastCoggableInterpretedBlockMethod
				ifTrue:
					[theMethod ~= lastUncoggableInterpretedBlockMethod ifTrue:
						[cogit cog: theMethod selector: objectMemory nilObject.
						 (self methodHasCogMethod: theMethod) ifTrue:
							[^self executeCogBlock: (self cogMethodOf: theMethod)
								closure: blockClosure
								mayContextSwitch: mayContextSwitch].
						 cogCompiledCodeCompactionCalledFor ifFalse:
							[lastUncoggableInterpretedBlockMethod := theMethod]]]
				ifFalse:
					[lastCoggableInterpretedBlockMethod := theMethod]]
		ifFalse:
			[self maybeFlagMethodAsInterpreted: theMethod].

	self assert: (self methodHasCogMethod: theMethod) not.
	"Because this is an uncogged method we need to continue via the interpreter.
	 We could have been reached either from the interpreter, in which case we
	 should simply return, or from a machine code frame or from a compiled
	 primitive.  In these latter two cases we must longjmp back to the interpreter.
	 The instructionPointer tells us which path we took.
	 If the sender was an interpreter frame but called through a (failing) primitive
	 then make sure we restore the saved instruction pointer and avoid pushing
	 ceReturnToInterpreterPC which is only valid between an interpreter caller
	 frame and a machine code callee frame."
	(inInterpreter := instructionPointer >= objectMemory startOfMemory) ifFalse:
		[instructionPointer = cogit ceReturnToInterpreterPC ifTrue:
			[instructionPointer := self iframeSavedIP: framePointer]].
	self push: instructionPointer.
	self push: framePointer.
	framePointer := stackPointer.
	self push: theMethod.
	self push: objectMemory nilObject. "FxThisContext field"
	self push: (self encodeFrameFieldHasContext: false isBlock: true numArgs: numArgs).
	self push: 0. "FoxIFSavedIP"
	"Because inst var access is not checked, we must follow the receiver in Spur to ensure it is valid."
	self push: (objectMemory followField: ReceiverIndex ofObject: outerContext).

	"Copy the copied values..."
	0 to: numCopied - 1 do:
		[:i|
		self push: (objectMemory
					fetchPointer: i + ClosureFirstCopiedValueIndex
					ofObject: blockClosure)].

	self assert: (self frameIsBlockActivation: framePointer).
	self assert: (self frameHasContext: framePointer) not.

	"The initial instructions in the block nil-out remaining temps."

	"the instruction pointer is a pointer variable equal to 
	method oop + ip + BaseHeaderSize 
	-1 for 0-based addressing of fetchByte 
	-1 because it gets incremented BEFORE fetching currentByte"
	closureIP := self quickFetchInteger: ClosureStartPCIndex ofObject: blockClosure.
	instructionPointer := theMethod + closureIP + objectMemory baseHeaderSize - 2.
	self setMethod: theMethod methodHeader: methodHeader.

	"Now check for stack overflow or an event (interrupt, must scavenge, etc)"
	switched := false.
	stackPointer < stackLimit ifTrue:
		[switched := self handleStackOverflowOrEventAllowContextSwitch: mayContextSwitch].
	self returnToExecutive: inInterpreter postContextSwitch: switched
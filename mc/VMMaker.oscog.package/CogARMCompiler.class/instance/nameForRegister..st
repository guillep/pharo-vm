printing
nameForRegister: reg "<Integer>"
	<doNotGenerate>
	reg < 0 ifTrue:
		[^super nameForRegister: reg].
	^#(LR SP PC CArg0Reg CArg0Reg CArg1Reg CArg2Reg CArg3Reg)
		detect: [:sym| (thisContext method methodClass classPool at: sym) = reg] 
		ifNone: [super nameForRegister: reg]
primitives
primitiveMPEG3EndOfVideo: fileHandle stream: aNumber
	| file result |

	"int mpeg3_end_of_video(mpeg3_t *file, int stream)"
	<var: #file type: 'mpeg3_t * '>
	self primitive: 'primitiveMPEG3EndOfVideo'
		parameters: #(Oop SmallInteger).

	file := self mpeg3tValueOf: fileHandle.
	file = nil ifTrue: [^0].
	aNumber < 0 ifTrue: [interpreterProxy success: false. ^nil].
	aNumber >= (self cCode: 'result = mpeg3_total_vstreams(file)') ifTrue: [
		interpreterProxy success: false.  ^0 ].


	self cCode: 'result = mpeg3_end_of_video(file,aNumber)'.
	^result asOop: Boolean

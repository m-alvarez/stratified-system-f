all: SysF.vo Metatheory.vo Correctness.vo Reduction.vo StrongNormalization.vo

SysF.vo: SysF.v
	coqc $<

StrongNormalization.vo: StrongNormalization.v SysF.vo Reduction.vo Metatheory.vo Correctness.vo
	coqc $<

%.vo: %.v SysF.vo
	coqc $<

clean:
	rm *.vo *.glob

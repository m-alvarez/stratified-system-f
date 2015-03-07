all: SysF.vo Metatheory.vo Correctness.vo Reduction.vo StrongNormalization.vo

SysF.vo: SysF.v
	coqc $<

%.vo: %.v SysF.vo
	coqc $<

clean:
	rm *.vo *.glob

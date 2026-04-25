COQPROJECT ?= _CoqProject
COQMAKEFILE ?= CoqMakefile

.PHONY: all clean coqmakefile

all: coqmakefile
	$(MAKE) -f $(COQMAKEFILE)

coqmakefile: $(COQMAKEFILE)

$(COQMAKEFILE): $(COQPROJECT)
	coq_makefile -f $(COQPROJECT) -o $(COQMAKEFILE)

clean: coqmakefile
	$(MAKE) -f $(COQMAKEFILE) clean

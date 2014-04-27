compilecoq := coqc -noglob -init-file coq.config
coq_makefile := coq_makefile
coq_top := coqtop -R . ""
coqsource := $(shell find src -name \*.v)
src_dir := src
output_dir := build

all_build_src := $(patsubst $(src_dir)/%.v,$(output_dir)/%.v,$(coqsource))
drop_build_dir := $(patsubst $(output_dir)/%,%,$(all_build_src))

.PHONY: clean

default: all

makefile: $(all_build_src)
	cd $(output_dir); $(coq_makefile) Haskell.v > Makefile.coq

console: $(all_build_src)
	cd $(output_dir); $(coq_top)

all: makefile
	cd $(output_dir); make -f Makefile.coq

# ch1 targets

$(output_dir):
	mkdir -p $(output_dir)

$(output_dir)/%.v: $(src_dir)/%.v $(output_dir)
	cp $< $@

# end ch1 targets

clean:
	rm -rfv $(output_dir)/*

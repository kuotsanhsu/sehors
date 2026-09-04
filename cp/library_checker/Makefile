CXXFLAGS += @compile_flags.txt

exes := $(shell sed '1,/^\#exes$$/d' .gitignore)

.PHONY: all test clean
all: $(exes)
txts := $(wildcard .*.txt)
test: $(txts:.txt=.pass)
clean:
	$(RM) .*.pass .*.log \
	$(exes)

.SECONDEXPANSION:
.%.pass: .%.txt $$(basename $$*)
	./$(lastword $^) < $^ | tee .$*.log
	@git diff --exit-code .$*.log
	@touch $@

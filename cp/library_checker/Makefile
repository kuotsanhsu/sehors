CXXFLAGS += -std=c++23
CXXFLAGS += -O2
#CXXFLAGS += -DDEBUG

exes := $(shell sed '1,/^\#exes$$/d' .gitignore)

.PHONY: all test clean
all: $(exes)
txts := $(wildcard .*.txt)
test: $(txts:.txt=.pass)
clean:
	$(RM) .*.pass \
	$(exes)

.SECONDEXPANSION:
.%.pass: .%.txt $$(basename $$*)
	./$(lastword $^) < $^
	@touch $@

# Cygwin / Linux differences:
ifdef WIN32
 EXE = .exe
else
 EXE = 
endif

CC = gcc -g -Wall# -DALLOC_DEBUG
LINK=$(CC)
O = o
CREATELIB = ar rc

TMPFILES =
MODULES = wpds sat semiring pds fa witness config ident heads hash# alloc
OBJECTS = $(MODULES:=.$(O))

WPDS = libwpds.a
default: $(WPDS)

$(WPDS): $(OBJECTS)
	$(CREATELIB) $(WPDS) $(OBJECTS)
	ranlib $(WPDS)

# Compiling:
%.$(O): %.c
	$(CC) -c $<

# clean
clean: 
	rm -f $(WPDS) $(OBJECTS) $(TMPFILES) \
              core core.* *.$(O) *.output mon.out gmon.out *.d .deps

# Dependencies

%.d: %.c
	$(SHELL) -ec '$(CC) -MM $*.c | sed '\''s/$*.o/& $*.d/g'\'' > $@'

DEPS = $(MODULES:=.d)

.deps: $(DEPS)
	echo " " $(DEPS) | \
	sed 's/[ 	][ 	]*/#include /g' | tr '#' '\012' > .deps

include .deps

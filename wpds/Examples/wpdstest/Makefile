# Cygwin / Linux differences:
ifdef WIN32
 EXE = .exe
else
 EXE = 
endif

CC = gcc -g -O3 -Wall -I$(INCLUDE)
LINK=$(CC)
O = o

TMPFILES =
WPDSDIR = ../..
WPDSLIB = wpds
INCLUDE = $(WPDSDIR)

TEST1 = wpdstest1$(EXE)
TEST2 = wpdstest2$(EXE)
default: $(TEST1) $(TEST2)

$(TEST1): wpdstest1.$(O) print.$(O) $(WPDSDIR)/lib$(WPDSLIB).a
	$(LINK) wpdstest1.$(O) print.$(O) -L$(WPDSDIR) -l$(WPDSLIB) -o $@

$(TEST2): wpdstest2.$(O) print.$(O) $(WPDSDIR)/lib$(WPDSLIB).a
	$(LINK) wpdstest2.$(O) print.$(O) -L$(WPDSDIR) -l$(WPDSLIB) -o $@

# Compiling:
%.$(O): %.c
	$(CC) -c $<

# clean
clean: 
	rm -f $(TEST1) $(TEST2) $(TMPFILES) \
              core core.* *.$(O) *.output mon.out gmon.out *.d .deps

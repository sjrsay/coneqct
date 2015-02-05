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

SPKITEST1 = spkitest1$(EXE)
SPKITEST2 = spkitest2$(EXE)
default: $(SPKITEST1) $(SPKITEST2)

$(SPKITEST1): spkitest1.$(O) print.$(O) $(WPDSDIR)/lib$(WPDSLIB).a
	$(LINK) spkitest1.$(O) print.$(O) -L$(WPDSDIR) -l$(WPDSLIB) -o $@

$(SPKITEST2): spkitest2.$(O) print.$(O) $(WPDSDIR)/lib$(WPDSLIB).a
	$(LINK) spkitest2.$(O) print.$(O) -L$(WPDSDIR) -l$(WPDSLIB) -o $@

# Compiling:
%.$(O): %.c
	$(CC) -c $<

# clean
clean: 
	rm -f $(SPKITEST1) $(SPKITEST2) $(TMPFILES) \
              core core.* *.$(O) *.output mon.out gmon.out *.d .deps

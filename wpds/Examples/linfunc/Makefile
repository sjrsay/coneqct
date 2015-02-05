# Cygwin / Linux differences:
ifdef WIN32
 EXE = .exe
else
 EXE = 
endif

CC = gcc -g -Wall -I$(INCLUDE)
LINK=$(CC)
O = o

TMPFILES =
WPDSDIR = ../..
WPDSLIB = wpds
INCLUDE = $(WPDSDIR)

LINCONST = linconst$(EXE)
default: $(LINCONST)

$(LINCONST): linconst.$(O) print.$(O) linfunc.$(O) $(INCLUDE)/wpds.h print.h linfunc.h $(WPDSDIR)/lib$(WPDSLIB).a
	$(LINK) linconst.$(O) print.$(O) linfunc.$(O) -L$(WPDSDIR) -l$(WPDSLIB) -o $@

# Compiling:
%.$(O): %.c
	$(CC) -c $<

# clean
clean: 
	rm -f $(LINCONST) $(TMPFILES) \
              core core.* *.$(O) *.output mon.out gmon.out *.d .deps

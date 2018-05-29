% M: Permutations with repetitions, by Eidon (2012)

\nocon % omit table of contents
%\datethis % print date on listing
%\pageno13
\def\overlinedR{\hbox{$\overline R$}}
\def\cardA{\hbox{card${}_{A}$}}
\def\cardM{\hbox{card${}_{M}$}}
\def\multisetM{\hbox{$M$}}
\def\pl{\hbox{Head${}_{\eightrm left}$}}
\def\pr{\hbox{Head${}_{\eightrm right}$}}
\def\Left{\hbox{the leftmost symbol of permutation $\multisetM$ i.e., $v$}}
\def\pprime{\hbox{$p'$}}

@f overlinedR TeX
@f cardA      TeX	
@f cardM      TeX	
@f multisetM  TeX	
@f pl         TeX
@f pr         TeX
@f Left       TeX
@f pprime     TeX

@* Permutations of a Multiset.
Here it is presented a C language function
to generate the successor of a given permutation according
to the algorithm discussed in \S2.
The multiset to be permuted is |M|. Function |successor()|
gets permutation $p$ and produces $p'$. Alphabet
|A| is normalized into the set of the first $m$ integer numbers.
A |main()| procedure recursively calls function |successor()|
up to |NULL| in order to produce permutations from $p_0^M$ to $p_{\infty}^M$.
Specific functions have been provided to compute the orbits of functions of those
permutations.

More information can be found in the articles
``A Formal Model and an Algorithm for Generating the Permutations of a Multiset,''
{\it WSEAS Transactions on Systems}, Vol. 1, No. 1;

\noindent
available at \pdfURL{https://goo.gl/zaatLv}{First paper}

\noindent
and ``Permutation Numbers,''
{\it Complex Systems}, Vol. 15, Issue 2;

\noindent
available at 
\pdfURL{https://goo.gl/Tefm8j}{Second paper}.

@c

@<prologue@>@/
@<global variables@>@/
@<successor permutation function@>@/
@<initialization and normalization@>@/
@<main@>@/



@ Starting section: headers, constants, and global variables.
In particular it is defined constant |EOP| (which stands for 
``\.{End Of Permutations}''), constant |MAX_MULTISET_CARD|,
an upper threshold for $n=\cardM$, and costant 
|MAX_ALPHABET_CARD|, an upper threshold for $m=\cardA$.

@d EOP        NULL
@d MAX_MULTISET_CARD   100
@d MAX_ALPHABET_CARD   10
@<prologue@>=

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>

@ A set of global variables have been introduced to minimize the parameter
exchange in function calls.
|M| is the string to be permuted, whose length is |cardM| byte (up to
|MAX_MULTISET_CARD|). |overlinedR| counts the occurences of each digit, so
it consists of |cardA| cells. The |offset| variable is used to normalize
back and forth the permuted string.

@<global variables@>=
char M[MAX_MULTISET_CARD];	/* multiset $M$ */
int  cardM;			/* $n$ i.e., its cardinality */
unsigned char *overlinedR;	/* multisubset $\overline R$ */
int cardA;	/* $m$, or the number of different symbols in Alphabet $A$ */

int offset;	/* ascii($a_1$), used for normalizing $M$ to $[0,\dots m-1]$ */
int ptoa(char*, int, int);
void initialize(char*, int*, int*, int*);
void printv(char*);
void printv1v2(char*);
void printv1v2v3(char*);
void printv1v2v3v4(char*);
void err(char*);

void printE(char*);
void printD(char*);
void printLogD(char*);
void print2D(char*);
void print3D(char*);
void printLR(char*);
void (*printOrbit)(char*);
char *fname;
FILE *f;
struct strobj { char *s, *sprime; };
typedef struct strobj obj;
void doNought(char *v) { return; }
unsigned char verbose = 0;

@* The successor operator.
Some sort of a Turing machine with two contiguous heads,
|pl| and |pr|, initially positioned on the last two characters
on the right end of the permutation.
They move leftward looking for a couple which is {\it not\/}
an inversion i.e. |*pl| is less than |*pr|. As they travel
across the string, |overlinedR| records the occurrences
of encountered characters. 
If a non-inversion is found,
$a_i$ stands below |pl|. It is substituted by the minimum
$a_k$ in |overlinedR| which is greater than $a_i$.
Then |overlinedR| is linearly scanned producing a zero
permutation of $\overline R$.
If all couples are inversions the string is decreasingly ordered
i.e., is a $p_{\infty}$ in which case |successor()| returns |EOP|.

@d Left v

@<successor...@>=
char* successor(char *v, int len)
{
  char *pl, *pr;
  int i, j, k;

  pl = &v[len-2], pr = &v[len-1]; /* move the head on the right end of |v| */
  bzero((char*)overlinedR, cardA); /*  $R\leftarrow\emptyset$ */

  @<inspect the permutation right-to-left looking for a non-inversion in $a_i$@>@;


  if (pr==Left)    /* no inversion means $p=p_{\infty}$, so $p'=\Lambda$ */
	return EOP;


  overlinedR[*pl]++; 		/* $R\cup\{a_i\}$ */

  @<looks for a $k$ which is the minimum $j$ such that $a_j>a_i$@>@;

  overlinedR[k]--;    /* $\{a_i\}\cup {\cal C}_R\{a_k\}$ */
  *pl++    = k;		/* $a_i \leftarrow a_k$ */

  @<builds $p_0^{\overline R}$@>@;

  return v;
}





@ Move the heads up to a couple (|pl|,|pr|) such that |*pl < *pr|
or the left end of the permutation.
Vector |overlinedR[]| counts the occurences of visited symbols.

@<inspect...@>=
while (pr != Left)
  {
    overlinedR[*pr]++;	  /* add the symbol to $\overline R$ */

    /* if (*pl-- < *pr--) break; /* shift to left both |pr| and |pl| */

    if (*pl < *pr) break;
    pr = pl--;
    /* alternatively, |if (*pl < *pr) break;|
                      |pr = pl--;|
     */
  }



@ if (|*pl|,|*pr|) is {\it not\/} an inversion then we need
to substitute |pl| (i.e., $a_i$) with the minimum of its
majorants.

@<looks for...@>=
for (k = *pl + 1; k<cardM; k++)
   if (overlinedR[k]) break;



@ Closings: we substituted $a_k$ for $a_i$ and now we
build an ordered postfix string i.e., a zero for $\overline R$.
This is made easy because we have |overlinedR| which
orderly counts the occurrence of the symbols in $\overline R$.

@<builds...@>=
for (i=0; i<cardA; i++)
  for (j=0; j<overlinedR[i]; j++)
    *pl++ = i;


@ Prints a permutation and computes $\nu(p)$.
@c
void printv(char *v) {
int i;
long l;
static long old_l;
static int num;

++num;
#define QUANTUM 1871100
if(num % QUANTUM == 0 || num % QUANTUM == 1)
	printf("%d\t", num);

for (l=0L, i=0; i<cardM; i++) {
	l = l * cardA + v[i];
	if(num % QUANTUM == 0 || num % QUANTUM == 1)
		putchar(v[i]+offset);
}
if(num % QUANTUM == 0 || num % QUANTUM == 1)
putchar('\n');

if (old_l)
	if (l-old_l>0)
	fprintf(f, "%f\n", log(l-old_l));
old_l=l;
}

void printE(char *v) {
int i;
long l;
static long old_l;
static int num;

++num;
if (verbose) printf("%d\t", num);

for (l=0L, i=0; i<cardM; i++) {
	l = l * cardA + v[i];
	if (verbose) putchar(v[i]+offset);
}
if (verbose) putchar('\n');

/* num(p) 
*/
fprintf(f, "%d\n", l);
old_l=l;
}

void printD(char *v) {
int i;
long l;
static long old_l;
static int num;

++num;
if (verbose) printf("%d\t", num);

for (l=0L, i=0; i<cardM; i++) {
	l = l * cardA + v[i];
	if (verbose) putchar(v[i]+offset);
}
if (verbose) putchar('\n');

/* D(num(p))
*/
fprintf(f, "%ld\n", l-old_l);
old_l=l;
}

void printLogD(char *v) {
int i;
long l;
static long old_l;
static int num;

++num;

if (verbose) printf("%d\t", num);

for (l=0L, i=0; i<cardM; i++) {
	l = l * cardA + v[i];
	if (verbose) putchar(v[i]+offset);
}
if (verbose) putchar('\n');

/* Log (D(num(p)))
 */
if (old_l)
   if (l-old_l>0)
      fprintf(f, "%f\n", log(l-old_l));
old_l=l;
}

void printLR(char *v) {
int i;
char *pl, *pr;
static char *p;

  if (p == NULL) {
    putchar('\\');
    putchar('{');
    for (i=0; i<cardM-1; i++) {
        putchar(v[i]+offset);
        putchar(',');
        putchar(' ');
    }
    putchar(v[i]+offset);
    printf("\\}, \\emptyset \\rightarrow \\linebreak\n");
    p = (char*)1;
  }
  pl = &v[cardM-2], pr = &v[cardM-1]; /* move the head on the right end of |v| */
  while (pr != v)
  {
    if (*pl < *pr) break;
    pr = pl--;
  }

  if (pr == v) {
    printf("\\linebreak\n");
    printf("\\emptyset, \\{\n");
    for (i=0; i<cardM-1; i++) {
        putchar(v[i]+offset);
        putchar(',');
        putchar(' ');
    }
    putchar(v[i]+offset);
    printf("\\}\n");
  } else {
    p = v;
    putchar('\\');
    putchar('{');
    while (p < pl) {
        putchar((*p++) + offset);
        putchar(',');
        putchar(' ');
    }
    putchar((*p++) + offset);
    putchar('\\');
    putchar('}');
    putchar(',');
    putchar(' ');
    putchar('\\');
    putchar('{');
    while (p < v + cardM - 1) {
        putchar((*p++) + offset);
        putchar(',');
        putchar(' ');
    }
    putchar((*p++) + offset);
    printf("\\} \\rightarrow\n");
  }
/*
 0123 
   LR   ->  {0,1, 2}, {3}
 0132 
  LR    ->  {0, 1}, {3, 2}
 0213
   LR   ->  {0, 2, 1}, {3}
 0231
  LR    ->  {0, 2}, {3, 1}
 0312
   LR   ->  {0, 3, 1}, {2}
 0321
 LR     ->  {0}, {3, 2, 1}
....         ......
 3210   ->  {} {3 2 1 0}
LR
*/

}


int ptoa(char *p, int l, int base)
{
	int i, res;

	for (res=i=0; i<l; i++)
		res = res * base + p[i];
	return res;
} 

void printv1v2(char *v) {
int l;
l = cardM;
assert (l % 2 == 0);
l >>= 1;
printf("%d, %d\n", ptoa(v, l, cardA), ptoa(v+l, l, cardA));
}

void printv1v2v3(char *v) {
int l;
l = cardM;
assert (l % 3 == 0);
l /= 3;
printf("%d, %d, %d\n",
ptoa(v, l, cardA), ptoa(v+l, l, cardA), ptoa(v+l+l, l, cardA));
}

void printv1v2v3v4(char *v) {
int l;
l = cardM;
assert (l % 4 == 0);
l /= 4;
printf("%d, %d, %d, %d\n",
ptoa(v, l, cardA), ptoa(v+l, l, cardA), ptoa(v+l+l, l, cardA), ptoa(v+3*l, l, cardA));
}

void dump(char* overlinedR) { int i;
printf("overlinedR=");
for (i = 0; i<cardM; i++)
   printf("%1d", overlinedR[i]);
printf("\n");
}

@ Initialization: the permutation is normalized, its length is
computed in |*sl|.

@<initial...@>=
 void initialize(char *s, int *sl, int *cl, int *offset)
{
  int min, max;
  int i;
  char *p=s;
  char c;

  *sl = strlen(s);

  min=255, max=0;	
  while (c = *p++)
    {
      if (c<min) min = c;
      if (c>max) max = c;
    }
  
  *offset = min;	/* offset will be used by |printv()| */

  *cl = max - min + 1;	/* \cardA, or the number of classes */

  overlinedR = (unsigned char *)malloc(*cl);

  /* normalization in 0..max-min */
  for (i=0; i < *sl; i++)
    s[i] -= min;
}

@ error print procedure
@c
void err(char *s) 
{
 fprintf(stderr, "error \"%s\" - bailing out.\n", s);
 exit(-1);
}




@ General main

@<main@>=

int main(int argc, char *argv[])
{
   int i, status;
   obj o;
   int compute(obj);

   if (argc<2) err("too few args. Valid args: [edloi23] and LR");

   o.sprime = '\0';
   for (i=1; i<argc; i++) {
      if (argv[i][0] == '-')
         switch (argv[i][1]) {
         case 'L': 
		   if (argv[i][2] == 'R') {
			   printOrbit = printLR ; 
			   printf("\\(\n");
		   } else err("args. Valid args: -[edloi23] and -LR\n");
			   break;
         case 'e': printOrbit = printE ; 
                   printf("printOrbit = num(p)\n");
                   break;
         case 'd': printOrbit = printD ; 
                   printf("printOrbit = D(num(p))\n");
                   break;
         case 'l': printOrbit = printLogD ; 
                   printf("printOrbit = log( D(num(p)) )\n");
                   break;
         case '2': printOrbit = print2D ; 
                   printf("printOrbit = ( num(p_l), num(p_r) )\n");
                   break;
         case '3': printOrbit = print3D ; 
                   printf("printOrbit = ( num(p_l), num(p_c), num(p_r) )\n");
                   break;
         case 'o': fname = strdup(argv[++i]);
                   if (fname == NULL) err("args");
                   break;
         case 'i': o.sprime = strdup(argv[++i]);
                   o.s = strdup(o.sprime);
                   break;
         case 'v': verbose = 1;
                   break;
         default:  err("args. Valid args: -[edloi23] and -LR\n");
         }
      else err("args. Valid args: [edloi23] and -LR\n");
   }

   if (printOrbit == NULL) {
      fprintf(stderr, "no orbit printing was chosen (-[edl23] or -LR)\n");
      if (fname != NULL)
         err("specify how to print orbits ([edl23] or -LR)");
      printOrbit = doNought;
   }

   if (o.sprime == '\0') {
      err("no input string");
   }

   if (fname == NULL)
      fname = "istogram";

   f=fopen(fname, "w");
   if (f==NULL) err("can't open istogram file");

   compute(o);
   if (printOrbit == printLR) printf("\\)\n");
   fclose(f);
   return 0;
}

int compute(obj o)
{
   char *p=o.s;
   char *pprime=o.sprime;
   int i;

   strcpy(M, p);
   initialize(M, &cardM, &cardA, &offset);
#ifdef PRINT
   printf("cardM=%d, cardA=%d, p=%s, pprime=%s\n", cardM, cardA, p, pprime);
#endif

   for (i=0; i<cardM; i++) pprime[i] -= offset;


   do {
   (*printOrbit)(M);

      if(!successor(M, cardM)) break;
   }  while (M && memcmp(M, pprime, cardM));



}

void print2D(char *v) {
int l;
l = cardM;
assert (l % 2 == 0);
l >>= 1;
fprintf(f, "%d, %d\n", ptoa(v, l, cardA), ptoa(v+l, l, cardA));
if (verbose) printf("%d, %d\n", ptoa(v, l, cardA), ptoa(v+l, l, cardA));
}

void print3D(char *v) {
int l;
l = cardM;
assert (l % 3 == 0);
l /= 3;
fprintf(f, "%d, %d, %d\n",
  ptoa(v, l, cardA), ptoa(v+l, l, cardA), ptoa(v+l+l, l, cardA));

if (verbose)
  printf("%d, %d, %d\n",
    ptoa(v, l, cardA), ptoa(v+l, l, cardA), ptoa(v+l+l, l, cardA));
}

/* END OF FILE PERM.W */

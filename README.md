# verify-todec
Formal check of Raffaello Guilietti's paper "Rendering doubles in Java"

This is an attempt to review mathematics behind contrubution to OpenJDK authored by Raffaello Guilietti.

Raffaello Guilietti has offered his code [1] to fix the problems described in the longstanding issue [2].
He also contributed the content of the CSR which Brian Burkhalter filed [3].
There are some pertinent posts to core-libs-dev in March [4], April [5] and May [6] as well.
In one of these the contributor posted a link to a background paper on the work [7].

In this repository I tried to formally check his paper using ACL2[8] proof checker.
Definitions and theorems from Section N of the pape are in file acl2/sectionN.lisp .
Proofs frpm sections 2-10 were checked by ACL2 completely.
Also cases fullCaseXS and fullCaseXM from the sections 2-11 were checked by ACL2.

At this moment a paper by Michel Hask [9] prompted us that it is possible to avoid multi-precision arithmetic
using approach from the paper. File acl2/cont-fractions.lisp formalizes some of these ideas in ACL2.
It considers a linear mapping alpha*d from range of naturals 0 <= d <= max-d to rationals.
It defines an algorithms which for given alpha and "max-d" returns bound "lo" and "hi"
how non-integer results of this mapping are frar from integer grid.
If approximate computations shows that alpha*d is very close to some integer m
m - hi < alpha * d < m + lo
then alpha * d is equal to m exactly.
Theorems frac-alpha-d-nonzero-bound-dp-correct and frac-alpha-d-nonzero-bound-sp-correct explicitly
state bounds lo and hi for float and double Java formats.
This fact is proved using contionous fractions.

Raffaello derived from this theorem that a table of powers of 5 with 126-bit precision is enough
to correctly implement DoubleToString conversion.
He designed a new implementation of DoubleToString and FlaotToString.
Class Natural with implementation of multi-presision natural is no more necessary. Conversions can be performed without memory allocation.
The WebRev of new Raffaello's algorith is in [10]. The CSR is in [11]. The discussion thread starts from [12].

One of the reviewer of Raffaello's alogirithm is Ulf Adams. He also developed fast float-to-string algorithm [13] with
a human proof of its correctness [14].

New Raffaello's and Ulf's algorithms looks similar. It would be interesting to compare them.
For example the problem of finding "lo" and "hi" is formulated as computing minimum and maximum of a modular product in [14].
Ideally it would be interesting to formally verify both of them though I am not sure if I find time for this.

Now I hope to prrepare in this repository an ACL2 proof of correctness of the new Raffaello's algoritn
which will supplement its human proof which probably will be contained in a new Raffaello's paper.


[1] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-April/052696.html

[2] https://bugs.openjdk.java.net/browse/JDK-4511638

[3] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-May/052934.html

[4] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-March/052355.html

[5] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-April/thread.html

[6] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-May/053088.html

[7] https://drive.google.com/drive/folders/1MErGSOaqDFw2q9rz48WlpBDKyZkLuUqj

[8] http://www.cs.utexas.edu/~moore/acl2/

[9] http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.85.8351&rep=rep1&type=pdf#page=114

[10] http://cr.openjdk.java.net/~bpb/4511638/webrev.00/

[11] https://bugs.openjdk.java.net/browse/JDK-8202555

[12] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-September/055698.html

[13] https://github.com/google/double-conversion

[14] https://dl.acm.org/citation.cfm?id=3192369
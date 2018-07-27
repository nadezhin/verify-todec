# verify-todec
Formal check of Raffaello Guilietti's paper "Rendering doubles in Java"

This is an attempt to review mathematics behind contrubution to OpenJDK authored by Raffaello Guilietti.

Raffaello Guilietti has offered his code [1] to fix the problems described in the longstanding issue [2].
He also contributed the content of the CSR which Brian Burkhalter filed [3].
There are some pertinent posts to core-libs-dev in March [4], April [5] and May [6] as well.
In one of these the contributor posted a link to a background paper on the work [7].

In this repository I try to formally check his paper using ACL2[8] proof checker.
Definitions and theorems from Section N of the pape are in file acl2/sectionN.lisp .

[1] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-April/052696.html

[2] https://bugs.openjdk.java.net/browse/JDK-4511638

[3] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-May/052934.html

[4] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-March/052355.html

[5] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-April/thread.html

[6] http://mail.openjdk.java.net/pipermail/core-libs-dev/2018-May/053088.html

[7] https://drive.google.com/drive/folders/1MErGSOaqDFw2q9rz48WlpBDKyZkLuUqj

[8] http://www.cs.utexas.edu/~moore/acl2/

module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelOrbit.Orbit

/-!
# The HS model core and its residual order-four orbit

For the exact core inside `localGroup 0`, the center is the embedded cyclic
factor, its commutator and Frattini subgroups are the common involution line,
and every square is one or that involution. The two central order-four roots
are identified explicitly. The alternating preimage fixes the center and
induces the compatible A₅ action on the central quotient. Its actual
conjugation action is transitive on the noncentral elements of order four.

The marked identities `commonInvolution_eq_e0` and `cyclicGenerator_square`
are retained through the public ModelCore import. Identification of the
alternating preimage with O², lifting to the central cover, and final source
assembly belong to the separate residual and centralizer-restriction owners.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

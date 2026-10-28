module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.Assembly

/-!
# The marked orthogonal case of K.3.1.2

`OrthogonalModel` retains an actual layer equivalence and binary intertwiner.
Its minus-orthogonal comparison uses the proved quadratic isometry. The root
partition, fixed spaces, and sharp actor calculations hold on the literal
source intersection T∩L. The outer field involution is a genuine K-transvection
with nonsingular moved line and centralizer SL₂(K); its elementary quadratic
actor X has rank s+1, fixed K-dimension two and ratio 2s/(s+1).

Odd extensions have q=2 and qhat=3/2. Even extensions with s>1 have
q=2s/(s+1) and qhat=min(3/2,2s/(s+1)). The complete quadratic threshold and
minimizing families are separate, and the threshold includes the rank-one
transvections when s=2. At s=1 the genuine five-point comparison gives either
the orthogonal A₅ action with q=2 and qhat=3/2, or the S₅ action with q=1,
commuting-transposition best offenders, and offenderSubgroup=G.

`SourceHypotheses.orthogonal_case` supplies the B.4.5 orthogonal row or the
S₅ case of B.4.2(5). Recognition of the marked Hermitian model remains the
separate rank-one recognition theorem's responsibility.

Source discrepancy: D.2.1 defines Q(G,V) by quadraticity and the threshold
r_A ≤ 2, not by minimizing the ratio. The printed final sentence of K.3.1.2
claiming every member is conjugate to X cannot hold: the preceding R_t has
ratio two and rank s, whereas X has rank s+1. Thus R_t is a threshold actor
and cannot be conjugate to X. Threshold classification and minimizing-actor
classification are stated separately. `fixedRoot_not_conjugate_outerActor`
formally proves this rank obstruction. No definition is changed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.1.2,
printed p.454; D.2.1, printed p.178; B.3.2(4) and B.4.5, printed pp.84 and 87.
-/

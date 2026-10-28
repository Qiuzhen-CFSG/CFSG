module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.AmbientActors.LayerGeometry
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.AmbientActors.LocalActors
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.AmbientActors.Ratios

/-!
# Ambient actions and outer actors for the orthogonal rank-one branch

The marked layer action embeds the source group in the semilinear SL₂
automorphism group, with cyclic field quotient. Odd extensions have all
elementary two-subgroups in L. Even extensions contain an actual involution
acting as canonical Hermitian conjugation, a K-transvection with nonsingular
moved line. Every outer involution is genuinely conjugate to it by L.

The literal layer centralizer is SL₂(K), its root centralizer is R_t, and
X=R_t⟨t⟩ is elementary of rank s+1. It is quadratic, fixes a K-plane, and has
ratio 2s/(s+1). Centralizer Sylow conjugacy places every outer elementary
actor in a layer conjugate of X. Rank-one actors fix a K-hyperplane and have
ratio s; larger actors fix a K-plane and have ratio 2s/rank(A).

For s>1 the outer threshold ranks are s and s+1, together with rank one when
s=2. The global quadratic minimizers in even extensions are exactly the
layer conjugates of X; this is separate from threshold membership. The proved
inner bounds give q=2 and qhat=3/2 in odd extensions, and q=2s/(s+1),
qhat=min(3/2,2s/(s+1)) in even extensions. Thus qhat>1 without an H.1 premise.
All action-realization and inner-bound premises are discharged.

Source: Aschbacher–Smith, K.3.1.2, printed p.454, and D.2.1, printed p.178,
combined manuscript of 1 March 2004. The printed assertion that every
threshold actor is conjugate to X is false and is not used. The s=1 model
comparison and final orthogonal family assembly remain with their consumer.
-/

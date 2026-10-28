module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Recovering a subgroup from an abelian quotient image

If `Q ≤ R`, the image of `R` is abelian, and the image of `Q` is
self-centralizing, the two images coincide. When the kernel lies in `Q`,
this equality lifts to `Q = R`. No normality or finiteness is needed.

This is the elementary content of the centralizer chain (*) in
Aschbacher–Smith, *The Classification of Quasithin Groups*, Lemma 14.2.21,
printed p.988: apply it to the quotient by the distinguished central line.
-/

namespace Subgroup

/-- An abelian overgroup of a self-centralizing image has the same preimage,
provided the smaller subgroup contains the kernel. -/
public theorem eq_of_abelian_map_of_centralizer_le
    {G D : Type*} [Group G] [Group D] (f : G →* D)
    (Q R : Subgroup G) (hker : f.ker ≤ Q) (hQR : Q ≤ R)
    [IsMulCommutative (R.map f)]
    (hcentralizer : centralizer (Q.map f : Set D) ≤ Q.map f) : Q = R := by
  have himage : R.map f ≤ Q.map f :=
    ((R.map f).le_centralizer.trans
      (centralizer_le (map_mono hQR))).trans hcentralizer
  exact le_antisymm hQR (by
    have h := map_le_map_iff.mp himage
    simpa only [sup_eq_left.mpr hker] using h)

end Subgroup

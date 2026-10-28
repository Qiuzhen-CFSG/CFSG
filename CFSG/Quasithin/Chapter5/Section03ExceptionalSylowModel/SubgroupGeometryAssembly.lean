module

public import CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel.NormalOutside
public import CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel.QuotientMaximal

/-!
# Exceptional Sylow subgroup geometry: assembled interface

This module re-exports the bound of sixteen and uniqueness of `Qbar` for
elementary abelian subgroups of the central quotient, together with the
identification of its elementary Thompson subgroup conditional on the
elementary and order facts for `Qbar`.

A nonabelian normal subgroup containing `Z` with elementary image in the
central quotient has two alternatives. Inside `S`, the root-coordinate
commutator determinant forces its center to be `Z`. Outside `S`, the
exponent-two condition and normality force the subgroup to equal `Q`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.7,
printed pp. 660--661 (PDF pp. 677--678).
-/

@[expose] public section

namespace Matrix.PSL3Four.SylowModel

/-- The two nonabelian normal-subgroup alternatives in the exceptional Sylow
model. The elementary hypothesis concerns the image modulo `C`. -/
theorem normal_nonabelian_alternatives (W : Subgroup T) (hn : W.Normal)
    (hZ : Z ≤ W) (helem : IsElementaryAbelian 2 (W.map quotient))
    (hnoncomm : ¬ IsMulCommutative W) :
    (W ≤ S ∧ (Subgroup.center W).map W.subtype = Z) ∨ W = Q := by
  by_cases hS : W ≤ S
  · exact Or.inl ⟨hS, center_nonabelian_le_S W hZ hS hnoncomm⟩
  · exact Or.inr (normal_outside_eq_Q W hn hZ helem hnoncomm hS)

end Matrix.PSL3Four.SylowModel

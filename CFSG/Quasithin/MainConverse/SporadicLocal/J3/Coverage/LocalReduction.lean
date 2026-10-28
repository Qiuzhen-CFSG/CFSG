module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Representatives
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Reducing the remaining J₃ normalizers to finite local calculations

An element normalizing a subgroup containing the standard involution can
first be matched on that involution by an element of a local candidate.
Their quotient centralizes the involution. Thus an ambient centralizer bound,
local transitivity, and a calculation inside the involution-centralizer
candidate bound the entire ambient normalizer.

The two small-class centralizers also reduce to finite data. The first
representative contains the standard involution; the other contains a
conjugate of the first under an element normalizing the elementary candidate.

Source: the three maximal two-locals of GLS, Number 3, Table 5.3h, p.269.
These are conditional reductions. The ambient centralizer bound and the
explicit local calculations must be proved for the fixed model words.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal

/-- Match an ambient normalizer element on `a` by a local element, leaving
a quotient in the standard involution centralizer. All remaining premises
concern elements of the fixed local candidates. -/
public theorem normalizer_le_local_of_transitive
    (B : Subgroup Model) (i : Fin 3) (haB : a ∈ B)
    (hC : centralizer ({a} : Set Model) ≤ localFamily 0)
    (hL : localFamily i ≤ normalizer (B : Set Model))
    (htrans : ∀ x ∈ B, x ≠ 1 → ∃ m ∈ localFamily i, (MulAut.conj m) a = x)
    (hstab : localFamily 0 ⊓ normalizer (B : Set Model) ≤ localFamily i) :
    normalizer (B : Set Model) ≤ localFamily i := by
  intro g hg
  have hga : (MulAut.conj g) a ∈ B := (hg a).mp haB
  have hga1 : (MulAut.conj g) a ≠ 1 := by
    intro h
    exact a_ne_one ((MulAut.conj g).injective (h.trans (map_one _).symm))
  obtain ⟨m, hm, hma⟩ := htrans _ hga hga1
  have hfix : (MulAut.conj (m⁻¹ * g)) a = a := by
    calc
      (MulAut.conj (m⁻¹ * g)) a =
          (MulAut.conj m).symm ((MulAut.conj g) a) := by
        simp [MulAut.conj_apply, mul_assoc]
      _ = a := by rw [← hma]; exact (MulAut.conj m).symm_apply_apply a
  have hcent : m⁻¹ * g ∈ centralizer ({a} : Set Model) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)
  have hnorm : m⁻¹ * g ∈ normalizer (B : Set Model) :=
    (normalizer (B : Set Model)).mul_mem
      ((normalizer (B : Set Model)).inv_mem (hL hm)) hg
  have hmem := (localFamily i).mul_mem hm (hstab ⟨hC hcent, hnorm⟩)
  simpa only [mul_inv_cancel_left] using hmem

/-- The order-four representative used for the affine branch contains `a`. -/
public theorem a_mem_elementaryRepresentative_one : a ∈ elementaryRepresentative 1 := by
  apply (le_sup_left : zpowers (elementaryGenerator 0) ≤
    zpowers (elementaryGenerator 0) ⊔ zpowers (elementaryGenerator 1))
  simpa only [elementaryGenerator_zero] using mem_zpowers (elementaryGenerator 0)

/-- The order-four representative used for the Thompson branch contains `a`. -/
public theorem a_mem_elementaryRepresentative_two : a ∈ elementaryRepresentative 2 := by
  apply (le_sup_left : zpowers (elementaryGenerator 0) ≤
    zpowers (elementaryGenerator 0) ⊔ zpowers (elementaryGenerator 2))
  simpa only [elementaryGenerator_zero] using mem_zpowers (elementaryGenerator 0)

/-- A calculation inside the involution-centralizer candidate and one
transporter inside N(E) give both small-class ambient centralizers. -/
public theorem small_centralizers_of_finite_calculations
    (hC : centralizer ({a} : Set Model) ≤ localFamily 0)
    (hcomm : elementaryCandidate ≤ centralizer (elementaryCandidate : Set Model))
    (hsmall : localFamily 0 ⊓ centralizer (elementaryRepresentative 1 : Set Model) ≤
      elementaryCandidate)
    (htransport : ∃ g : Model, g ∈ normalizer (elementaryCandidate : Set Model) ∧
      (elementaryRepresentative 1).map (MulAut.conj g).toMonoidHom ≤
        elementaryRepresentative 3) :
    centralizer (elementaryRepresentative 1 : Set Model) = elementaryCandidate ∧
      centralizer (elementaryRepresentative 3 : Set Model) = elementaryCandidate := by
  have hsmallC : centralizer (elementaryRepresentative 1 : Set Model) ≤ localFamily 0 :=
    (centralizer_le (Set.singleton_subset_iff.mpr a_mem_elementaryRepresentative_one)).trans hC
  have hCOne : centralizer (elementaryRepresentative 1 : Set Model) = elementaryCandidate :=
    le_antisymm (fun x hx => hsmall ⟨hsmallC hx, hx⟩)
      (hcomm.trans (centralizer_le (elementaryRepresentative_le_elementaryCandidate 1)))
  refine ⟨hCOne, le_antisymm ?_ ?_⟩
  · obtain ⟨g, hg, hBD⟩ := htransport
    intro x hx
    have hxB : (MulAut.conj g).symm x ∈
        centralizer (elementaryRepresentative 1 : Set Model) := by
      intro y hy
      apply (MulAut.conj g).injective
      have h := hx ((MulAut.conj g) y) (hBD ⟨y, hy, rfl⟩)
      simpa only [map_mul, MulEquiv.apply_symm_apply] using h
    rw [hCOne] at hxB
    have hmem := (hg ((MulAut.conj g).symm x)).mp hxB
    change (MulAut.conj g) ((MulAut.conj g).symm x) ∈ elementaryCandidate at hmem
    rwa [MulEquiv.apply_symm_apply] at hmem
  · exact hcomm.trans (centralizer_le (elementaryRepresentative_le_elementaryCandidate 3))

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage

module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Linarith

/-!
# Elementary subgroups in a pair-swapping extension

Let `S` be a normal subgroup of index two in a finite subgroup `N`. Suppose
every elementary abelian two-subgroup of `S` lies in one of `A` and `B`, whose
intersection has order four, and elements of `N` outside `S` interchange them.
If the centralizer of their intersection in `N` lies in `S`, every elementary
abelian subgroup of `N` of order at least eight already lies in `S`.

For such a subgroup `E`, the relative-index bound and Lagrange's theorem give
`|E ∩ S| ≥ 4`. An element of `E` outside `S` fixes this intersection pointwise
while interchanging the pair, forcing `E ∩ S ≤ A ∩ B`. Equality follows from
the cardinalities, contradicting the centralizer hypothesis.

This general finite-group lemma supplies the elementary-subgroup exclusion
underlying Stellmacher's Section 11 case (II) Thompson equality; see
`refs/latex/stellmacher-n-group.tex`, lines 2089–2095. It uses no model-group
classification or Thompson monotonicity.
-/

namespace Subgroup

/-- Large elementary abelian subgroups cannot leave an index-two subgroup
when the outside coset swaps a covering pair with the stated centralizer bound. -/
public theorem elementary_le_of_swapped_pair
    {G : Type*} [Group G] [Finite G] (S N A B : Subgroup G)
    (_hSN : S ≤ N) (_hNS : N ≤ normalizer (S : Set G))
    (hindex : S.relIndex N = 2) (_hAS : A ≤ S) (_hBS : B ≤ S)
    (hcard : Nat.card (A ⊓ B : Subgroup G) = 4)
    (hpair : ∀ E : Subgroup G, E ≤ S → IsElementaryAbelian 2 E → E ≤ A ∨ E ≤ B)
    (hswap : ∀ x ∈ N, x ∉ S →
      A.map (MulAut.conj x).toMonoidHom = B ∧
        B.map (MulAut.conj x).toMonoidHom = A)
    (hcentralizer : N ⊓ centralizer ((A ⊓ B : Subgroup G) : Set G) ≤ S)
    (E : Subgroup G) (hEN : E ≤ N) (hE : IsElementaryAbelian 2 E)
    (hlarge : 8 ≤ Nat.card E) : E ≤ S := by
  let := hE
  have hinterElementary : IsElementaryAbelian 2 (E ⊓ S : Subgroup G) := by
    refine {
      toIsMulCommutative := .of_setLike_mul_comm fun left hleft right hright =>
        congrArg Subtype.val ((IsMulCommutative.is_comm (M := E)).comm
          ⟨left, hleft.1⟩ ⟨right, hright.1⟩)
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
    }
    intro element
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (A := E) element.val element.property.1
  have hindexBound : S.relIndex E ≤ 2 := by
    simpa only [hindex] using
      (relIndex_le_of_le_right (H := S) hEN (by omega : S.relIndex N ≠ 0))
  have hcardProduct : S.relIndex E * Nat.card (E ⊓ S : Subgroup G) = Nat.card E := by
    have hprod := ((E ⊓ S).subgroupOf E).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : E ⊓ S ≤ E)).toEquiv] at hprod
    change (E ⊓ S).relIndex E * Nat.card (E ⊓ S : Subgroup G) = Nat.card E at hprod
    simpa only [inf_relIndex_left] using hprod
  have hinterLarge : 4 ≤ Nat.card (E ⊓ S : Subgroup G) := by
    nlinarith
  intro outside houtside
  by_contra hnotS
  have hswapped := hswap outside (hEN houtside) hnotS
  have hfixed (element : G) (helement : element ∈ E ⊓ S) :
      (MulAut.conj outside).toMonoidHom element = element := by
    change outside * element * outside⁻¹ = element
    rw [setLike_mul_comm houtside helement.1, mul_inv_cancel_right]
  have hinterPair : E ⊓ S ≤ A ⊓ B := by
    rcases hpair (E ⊓ S) inf_le_right hinterElementary with hA | hB
    · intro element helement
      refine ⟨hA helement, ?_⟩
      rw [← hswapped.1]
      exact mem_map.mpr ⟨element, hA helement, hfixed element helement⟩
    · intro element helement
      refine ⟨?_, hB helement⟩
      rw [← hswapped.2]
      exact mem_map.mpr ⟨element, hB helement, hfixed element helement⟩
  have hinterEq : E ⊓ S = A ⊓ B :=
    eq_of_le_of_card_ge hinterPair (by simpa only [hcard] using hinterLarge)
  apply hnotS
  apply hcentralizer
  refine ⟨hEN houtside, mem_centralizer_iff.mpr ?_⟩
  intro element helement
  have hin : element ∈ E ⊓ S := by rwa [hinterEq]
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := E)).comm
    ⟨element, hin.1⟩ ⟨outside, houtside⟩)

end Subgroup

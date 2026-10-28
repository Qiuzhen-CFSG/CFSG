module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The external index-three Borel deduction

Source: Aschbacher–Smith 13.8.20, printed p.954 (combined manuscript,
1 March 2004), the even-degree L₂ branch of alternative (a).

If B_C O₂(B) lies in K and has index three in BX, with X outside K,
then the subgroup (BX) ∩ K equals B_C O₂(B). Consequently B is contained
in that subgroup. Both B and B_C are actual two-residuals; taking the
two-residual removes the normalizing two-group supplement and gives B ≤ B_C.

The required placements and normalization are explicit. They still have to
be derived from the source setup and the Borel model; the index alone does
not imply them. Only relative normality is used.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem le_of_external_index_three
    (B C K X : Subgroup G)
    (hBK : B ≤ K) (hXK : ¬ X ≤ K)
    (hN : C ⊔ B.pCoreIn 2 ≤ K)
    (hCJ : C ≤ B ⊔ X)
    (hindex : (C ⊔ B.pCoreIn 2).relIndex (B ⊔ X) = 3) :
    B ≤ C ⊔ B.pCoreIn 2 := by
  let N := C ⊔ B.pCoreIn 2
  let J := B ⊔ X
  have hNJ : N ≤ J := sup_le hCJ ((pCoreIn_le 2 B).trans le_sup_left)
  have hm := relIndex_mul_relIndex N (J ⊓ K) J (le_inf hNJ hN) inf_le_left
  rw [hindex] at hm
  have hproper : (J ⊓ K).relIndex J ≠ 1 := by
    intro hi
    exact hXK (le_sup_right.trans ((relIndex_eq_one.mp hi).trans inf_le_right))
  have hp : (N.relIndex (J ⊓ K) * (J ⊓ K).relIndex J).Prime := hm ▸ Nat.prime_three
  have hi : N.relIndex (J ⊓ K) = 1 := by
    rcases Nat.prime_mul_iff.mp hp with ⟨_, hi⟩ | ⟨_, hi⟩
    · exact (hproper hi).elim
    · exact hi
  exact (le_inf le_sup_left hBK).trans (relIndex_eq_one.mp hi)

/-- The even-degree linear branch: the index three and external X first
put B in B_C O₂(B); two-perfectness then removes the two-group supplement. -/
theorem borel_le_centralizingResidual_of_external_index
    (B₀ L₁ L K X : Subgroup G)
    (hBK : borelResidual B₀ ≤ K) (hXK : ¬ X ≤ K)
    (hN : centralizingResidual (borelResidual B₀) L₁ L ⊔
      (borelResidual B₀).pCoreIn 2 ≤ K)
    (hCJ : centralizingResidual (borelResidual B₀) L₁ L ≤ borelResidual B₀ ⊔ X)
    (hnorm : (borelResidual B₀).pCoreIn 2 ≤
      normalizer (centralizingResidual (borelResidual B₀) L₁ L))
    (hindex : (centralizingResidual (borelResidual B₀) L₁ L ⊔
      (borelResidual B₀).pCoreIn 2).relIndex (borelResidual B₀ ⊔ X) = 3) :
    borelResidual B₀ ≤ centralizingResidual (borelResidual B₀) L₁ L := by
  let B := borelResidual B₀
  let C := centralizingResidual B L₁ L
  have hBC : B ≤ C ⊔ B.pCoreIn 2 :=
    le_of_external_index_three B C K X hBK hXK hN hCJ hindex
  have hB : IsPPerfect 2 B := isPPerfect_embedded_pResidual 2 B₀
  have hC : IsPPerfect 2 C := isPPerfect_embedded_pResidual 2 (borelCentralizer B L₁ L)
  have hm := embedded_pResidual_mono 2 hBC
  rw [embedded_pResidual_join_pGroup C (B.pCoreIn 2) hC (isPGroup_pCoreIn 2 B) hnorm,
    (pResidual_eq_top_iff 2 B).mpr hB, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction

end

module
public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# Elementary actors on an elementary group of order eight

The full automorphism group is GL₃(2), whose elementary two-subgroups have
order at most four. Restricting the literal normalizer action therefore
bounds |A:C_A(W)| by four for every elementary actor A on W of order eight.
This excludes the natural L₃(2) row in the final paragraph of
Aschbacher–Smith 13.4.1, printed p.915.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
/-- The actual conjugation image of an elementary actor on an eight-group has order at most four. -/
theorem elementary_eight_centralizer_index_le_four
    (A W : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 W]
    (hAW : A ≤ normalizer (W : Set G)) (hW : Nat.card W = 8) :
    (A ⊓ centralizer (W : Set G)).relIndex A ≤ 4 := by
  let φ : A →* MulAut W := W.normalizerMonoidHom.comp (inclusion hAW)
  have hk : φ.ker = (centralizer (W : Set G)).subgroupOf A := by
    ext a
    change W.normalizerMonoidHom ⟨a.val,hAW a.property⟩ = 1 ↔ _
    change (⟨a.val,hAW a.property⟩ : normalizer (W : Set G)) ∈
      W.normalizerMonoidHom.ker ↔ _
    rw [Subgroup.normalizerMonoidHom_ker]
    rfl
  have hi : Nat.card φ.range = (A ⊓ centralizer (W : Set G)).relIndex A := by
    rw [←index_ker,hk]
    change (centralizer (W : Set G)).relIndex A = _
    rw [inf_relIndex_left]
  obtain ⟨e⟩ := elementaryEight_mulAut_equiv_GL W hW
  let b := e.trans (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv)
  have hr : primeRank 2 (MulAut W) ≤ 2 := by
    rw [primeRank_equiv 2 b]
    exact (Matrix.PSL3Even.two_rank (ZMod 2) (n := 1) (by decide) (by simp)).le
  let : IsElementaryAbelian 2 φ.range :=
    IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  rw [← hi]
  exact (primeRank_le_iff_elementary_card_le _).mp hr φ.range inferInstance
end Theory.GroupTheory

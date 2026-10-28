module
public import Theory.GroupAction.ThompsonAB
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Components in centralizers of p-subgroups

If a finite group has a self-centralizing normal p-subgroup K, the centralizer
of any p-subgroup B has no components. The normal-subgroup dichotomy makes a
putative component centralize C_K(B). Thompson's residual A × B lemma then
makes it centralize K, forcing that perfect component into a p-group.

Source: Thompson's A × B lemma, Aschbacher–Smith A.1.18, printed p.24,
and the component normal-subgroup dichotomy, GLS volume 2, Theorem 3.5.
The J₄ whole-two-action inspection in E.6.18 is an application.
-/

public section
open Subgroup
namespace Theory.GroupTheory

private theorem perfect_isPPerfect {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] (p : ℕ) [Fact p.Prime] : IsPPerfect p G := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (G ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (G ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (G ⧸ N) inferInstance

/-- A p-subgroup centralizer in a group with a self-centralizing normal p-subgroup
has no components. -/
theorem not_isComponent_centralizer_of_normal_pGroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (K B : Subgroup G) [K.Normal]
    (hK : IsPGroup p K) (hB : IsPGroup p B)
    (hC : centralizer (K : Set G) ≤ K)
    (L : Subgroup (centralizer (B : Set G))) :
    ¬ IsComponent (centralizer (B : Set G)) L := by
  intro hL
  let F := centralizer (B : Set G)
  let A := L.map F.subtype
  let N := K.subgroupOf F
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hnot (hAK : A ≤ K) : False := by
    have hpA : IsPGroup p A := hK.to_le hAK
    have hpL : IsPGroup p L := hpA.of_equiv (L.equivMapOfInjective F.subtype F.subtype_injective).symm
    let : Group.IsNilpotent L := hpL.isNilpotent
    exact Group.IsPerfect.not_isSolvable L inferInstance
  have hLN : ⁅L, N⁆ = ⊥ := by
    rcases hL.normal_dichotomy N with h | h
    · exact (hnot (by rintro _ ⟨l, hl, rfl⟩; exact h hl)).elim
    · exact h
  have hAB : ⁅B, A⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (map_subtype_le L)
  have hfix : K ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G) := by
    intro k hk a ha
    obtain ⟨l, hl, rfl⟩ := ha
    have hc := commutator_eq_bot_iff_le_centralizer.mp hLN hl
      (⟨k, hk.2⟩ : F) hk.1
    exact (congrArg Subtype.val hc).symm
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := F.subtype.subgroupMap L) (F.subtype.subgroupMap_surjective L)
  have hKA := thompson_a_times_b_centralizer A B K hB hK
    ((pResidual_eq_top_iff p A).mpr (perfect_isPPerfect p))
    le_normalizer_of_normal le_normalizer_of_normal hAB hfix
  apply hnot
  apply le_trans _ hC
  apply commutator_eq_bot_iff_le_centralizer.mp
  rwa [commutator_comm]

end Theory.GroupTheory

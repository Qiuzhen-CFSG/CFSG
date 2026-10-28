module
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import CFSG.Quasithin.ChapterA.Section02.OddPrimeRank
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.DisjointCommutingProduct

/-! A quasisimple group of cubic central-quotient rank two cannot embed
in a product of groups of cubic rank one.  A nontrivial projection has
central kernel, so its central quotient retains the rank obstruction.
This excludes the prime-pair containing row at the second pumpup. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {P A B : Type*} [Group P] [Finite P] [IsQuasisimple P]
  [Group A] [Finite A] [Group B] [Finite B]

private theorem central_quotient_rank_le_one_of_nontrivial_projection
    (f : P →* A) (hne : f.range ≠ ⊥) (hr : primeRank 3 A ≤ 1) :
    primeRank 3 (P ⧸ center P) ≤ 1 := by
  let R := f.range
  let : Nontrivial R := (nontrivial_iff_ne_bot _).mpr hne
  let : IsQuasisimple R := IsQuasisimple.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let e : (P ⧸ center P) ≃* (R ⧸ center R) :=
    IsQuasisimple.centralQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective
  have hR : primeRank 3 R ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 R.subtype R.subtype_injective).trans hr
  rw [primeRank_equiv 3 e]
  exact (PrimeRank.le_of_surjective_of_source_le_one (by decide : (3 : ℕ) ≠ 2)
    (QuotientGroup.mk' (center R)) (QuotientGroup.mk'_surjective _) hR).trans hR

theorem no_rank_two_quasisimple_embedding_in_rank_one_pair
    (hr : 2 ≤ primeRank 3 (P ⧸ center P))
    (hA : primeRank 3 A ≤ 1) (hB : primeRank 3 B ≤ 1)
    (f : P →* A × B) (hf : Function.Injective f) : False := by
  let fA := (MonoidHom.fst A B).comp f
  let fB := (MonoidHom.snd A B).comp f
  by_cases hneA : fA.range ≠ ⊥
  · have hh := central_quotient_rank_le_one_of_nontrivial_projection fA hneA hA
    omega
  have hneB : fB.range ≠ ⊥ := by
    intro hzero
    have hzeroA : fA.range = ⊥ := not_ne_iff.mp hneA
    have hP : ∀ x : P, x = 1 := by
      intro x
      apply hf
      apply Prod.ext
      · have h : fA x ∈ fA.range := ⟨x,rfl⟩
        rw [hzeroA,mem_bot] at h
        rw [map_one]
        change fA x = 1
        exact h
      · have h : fB x ∈ fB.range := ⟨x,rfl⟩
        rw [hzero,mem_bot] at h
        rw [map_one]
        change fB x = 1
        exact h
    let : Subsingleton P := ⟨fun x y => (hP x).trans (hP y).symm⟩
    let : IsSimpleGroup (P ⧸ center P) := IsQuasisimple.simple
    let : Nontrivial P := (QuotientGroup.mk'_surjective (center P)).nontrivial
    exact not_subsingleton P inferInstance
  have hh := central_quotient_rank_le_one_of_nontrivial_projection fB hneB hB
  omega

theorem no_rank_two_quasisimple_subgroup_of_exchanged_rank_one_pair
    {G : Type*} [Group G] [Finite G]
    (P A : Subgroup G) [IsQuasisimple P]
    (hr : 2 ≤ primeRank 3 (P ⧸ center P))
    (hA : IsComponent G A) (hzA : center A = ⊥) (hrA : primeRank 3 A ≤ 1)
    (t : G) (hne : A.map (MulAut.conj t).toMonoidHom ≠ A)
    (hP : P ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) : False := by
  let B := A.map (MulAut.conj t).toMonoidHom
  have hc : A ≤ centralizer (B : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hA.commutator_eq_bot_of_ne (hA.map_conj t) hne.symm)
  have hd : Disjoint A B := by
    apply disjoint_def.mpr
    intro x hxA hxB
    have hz : (⟨x,hxA⟩ : A) ∈ center A := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hc y.property x hxB).symm
    rw [hzA,mem_bot] at hz
    exact congrArg Subtype.val hz
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  have hrB : primeRank 3 B ≤ 1 := by
    rwa [primeRank_equiv 3 ((MulAut.conj t).subgroupMap A)] at hrA
  exact no_rank_two_quasisimple_embedding_in_rank_one_pair hr hrA hrB
    (e.symm.toMonoidHom.comp (inclusion hP))
    (e.symm.injective.comp (inclusion_injective hP))
end CFSG.Quasithin.Chapter2.Section05.Overcomponents

module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Components.LocalRestrictions
public import Theory.Quasithin.ComponentRanks.CentralProducts

/-!
# The actual pair forced by two centered source components

Two components with nontrivial centers have ordinary three-rank two and
centers of order three. Quasithinness forces their embedded centers to
coincide and excludes every third component. Their intersection is the
common center, and their product is the ambient group. Consequently the
ambient center has order three and the original offending section is
exactly its central quotient.

No unitary model or prime-core identity is assumed. Identifying the two
components from their local rank at most one is the remaining model sieve.

Source: Aschbacher–Smith A.2.12(II), printed p.37.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.centered_component_pair_structure
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    (hcovers : SQTKStructure.OrdinarySource.RemainingOddCoverInputs.{u})
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hzC : center C ≠ ⊥) (hzD : center D ≠ ⊥) :
    C ⊔ D = ⊤ ∧
      (center C).map C.subtype = (center D).map D.subtype ∧
      C ⊓ D = (center C).map C.subtype ∧ Nat.card (center G) = 3 := by
  have hcardC := h.component_center_card_three ih hsemi hn hcovers hC hzC
  have hcardD := h.component_center_card_three ih hsemi hn hcovers hD hzD
  have hrC := (h.component_threeRanks_eq_two ih hsemi hn hcovers hC hzC).1.ge
  have hrD := (h.component_threeRanks_eq_two ih hsemi hn hcovers hD hzD).1.ge
  have he := hC.centers_eq_of_cubic_centers hD hne h.1 hcardC hcardD hrD
  have hc : C ≤ centralizer (D : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hC.commutator_eq_bot_of_ne hD hne)
  have hi : C ⊓ D = (center C).map C.subtype := by
    apply le_antisymm
    · rintro x ⟨hxC, hxD⟩
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hc y.property x hxD).symm
    · apply le_inf (map_subtype_le _)
      rw [he]
      exact map_subtype_le _
  have hic : Nat.card (C ⊓ D : Subgroup G) ≤ 3 := by
    rw [hi, card_map_of_injective C.subtype_injective, hcardC]
  have hg := hC.sup_eq_top_of_cubic_intersection hD hne hsemi h.1 hic hrC hrD
  refine ⟨hg, he, hi, ?_⟩
  rw [center_eq_sup_center_of_commuting C D hc hg, ← he, sup_idem,
    card_map_of_injective C.subtype_injective, hcardC]

theorem CounterexampleToTheoremA.section_equiv_centerQuotient_of_center_card_three
    {K : GroupClass.{u}} (h : CounterexampleToTheoremA K G S p)
    (ih : TheoremAOnProperSections K G) (hsemi : IsSemisimple G)
    (hcard : Nat.card (center G) = 3) : Nonempty (S ≃* G ⧸ center G) := by
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  have hk : f.ker ≤ center G := by
    rw [← fittingSubgroup_eq_center_of_componentLayer_eq_top hsemi,
      ← h.center_preimage_eq_fitting ih f hf]
    intro x hx
    change f x ∈ center S
    rw [show f x = 1 from hx]
    exact one_mem _
  have hc : Nat.card f.ker = 3 := by
    have hd : Nat.card f.ker ∣ 3 := hcard ▸ card_dvd_of_le hk
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with he | he
    · have hh := h.prime_dvd_cover_kernel ih f hf
      rw [he] at hh
      exact (h.2.2.2.2.1.not_dvd_one hh).elim
    · exact he
  have he : f.ker = center G := eq_of_le_of_card_ge hk (by rw [hc, hcard])
  exact ⟨(QuotientGroup.liftEquiv (center G) hf he.symm).symm⟩

end CFSG.Quasithin.ChapterA.Section02

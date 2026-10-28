module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.TwoCentralizerRank
public import Theory.Representation.BinaryOffender.CommutingSectionDegree

/-!
# FF alternatives with large commuting sections

Apply the source B.5 classification to a faithful offender-generated actor
centralizing a fixed-free perfect group whose nonzero sections have degree at
least 24. The displacement bound excludes the small group cases; the moved
dimension bound excludes the small module cases, and perfect centralization
excludes Irr⁺. The actual two-factor and doubled natural SL₃ cases remain.

Source: Aschbacher–Smith, B.5 and the quiet branch of 10.1.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [Finite D] [FiniteDimensional (ZMod 2) V] in
theorem quasisimple_double_of_large_moved_sections
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hn : ¬ IsIrrPlus ρ K (subspaceCommutator ρ ⊤ K))
    (hd : 24 ≤ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K)) :
    ∃ F : BinaryField, K = ⊤ ∧
      Nonempty (ActionEquiv (c.sectionData.space.toRepresentation.comp K.subtype)
        (repeated (linearNatural F 3) 2)) := by
  change ¬ IsIrrPlus ρ K (moved ρ K) at hn
  change 24 ≤ Module.finrank (ZMod 2) (moved ρ K) at hd
  cases c.clause_one with
  | irreducible hi _ _ _ _ =>
    exact (hn (c.sectionData.space_eq ▸ hi)).elim
  | doubleThree F hK e _ _ => exact ⟨F,hK,⟨e⟩⟩
  | naturalDual d hdim _ he =>
    obtain ⟨e⟩ := he
    have hh : Module.finrank (ZMod 2) c.sectionData.space.toSubmodule = d+d := by
      rw [e.linearEquiv.finrank_eq]
      change Module.finrank (ZMod 2) ((Fin d → ZMod 2) × Module.Dual (ZMod 2) (Fin d → ZMod 2)) = d+d
      rw [Module.finrank_prod,Subspace.dual_finrank_eq]
      simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
    rw [c.sectionData.space_eq] at hh
    rcases hdim with rfl | rfl <;> omega
  | repeatedNatural d r hdim hr hrb _ he =>
    obtain ⟨e⟩ := he
    have hh : Module.finrank (ZMod 2) c.sectionData.space.toSubmodule = r*d := by
      rw [e.linearEquiv.finrank_eq]
      change Module.finrank (ZMod 2) (Fin r → Fin d → ZMod 2) = r*d
      simp only [Module.finrank_pi_fintype,Module.finrank_self,
        Fintype.card_fin,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
    rw [c.sectionData.space_eq] at hh
    rcases hdim with rfl | rfl <;> omega

end CFSG.Quasithin.ChapterB.SourceInduction

namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {Q D V : Type*} [Group Q] [Finite Q] [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The two remaining actual B.5 module cases after large-section exclusion. -/
@[expose] def LargeSectionFFCases (σ : Representation (ZMod 2) D V) : Prop :=
  Nonempty (SourceTwoFactorCase σ) ∨
    ∃ c : ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting D),
      ∃ F : BinaryField, generalizedFitting D = ⊤ ∧
        Nonempty (ActionEquiv
          (c.sectionData.space.toRepresentation.comp (generalizedFitting D).subtype)
          (repeated (linearNatural F 3) 2))

omit [Finite Q] in
theorem ff_rows_of_large_commuting_perfect
    (ρ : Representation (ZMod 2) Q V) (hρ : Function.Injective ρ)
    (S : Subgroup Q) [Group.IsPerfect S]
    (hfix : fixedSpace ρ S = ⊥)
    (hdegree : ∀ U : Subrepresentation (ρ.comp S.subtype), U ≠ ⊥ →
      24 ≤ Module.finrank (ZMod 2) U.toSubmodule)
    (f : D →* Q) (hf : Function.Injective f)
    (hc : f.range ≤ centralizer (S : Set Q))
    (hcore : pCore 2 D = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple D)
    (hgen : offenderSubgroup (ρ.comp f) = ⊤)
    (hff : IsFFModule (ρ.comp f)) :
    LargeSectionFFCases (ρ.comp f) := by
  let σ := ρ.comp f
  have hfaith : Function.Injective σ := hρ.comp hf
  have hno (K : Subgroup D) :
      ¬ IsIrrPlus σ K (subspaceCommutator σ ⊤ K) := by
    intro h
    have hh : IsIrrPlus ρ (K.map f) (subspaceCommutator σ ⊤ K) :=
      h.of_intertwining σ ρ (f.subgroupMap K) (f.subgroupMap_surjective K)
        LinearMap.id Function.injective_id (fun _ _ => rfl) (Submodule.map_id _)
    rw [subspaceCommutator_comp_map] at hh
    exact not_irrPlus_moved_of_commuting_perfect ρ S (K.map f) hfix
      (le_centralizer_iff.mp ((map_le_range f K).trans hc)) hh
  have hkernel (K : Subgroup D) (hK : K ≠ ⊥) : ¬ K.map f ≤ ρ.ker := by
    intro h
    apply hK
    apply bot_unique
    intro k hk
    apply hf
    apply hρ
    exact (h (mem_map_of_mem f hk)).trans (by simp)
  have hdim (K : Subgroup D) (hK : K ≠ ⊥) :
      24 ≤ Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ K) := by
    rw [subspaceCommutator_comp_map]
    exact degree_le_moved_finrank_of_commuting ρ S (K.map f) hdegree
      (hkernel K hK) ((map_le_range f K).trans hc)
  have hcard : 2^24 ≤ Nat.card D := by
    obtain ⟨A,hA⟩ := hff
    have hd := degree_le_fixedCodim_of_commuting ρ S (A.map f) hdegree
      (hkernel A hA.1.1) ((map_le_range f A).trans hc)
    have he := fixedCodim_map_equivariant σ ρ f (LinearEquiv.refl (ZMod 2) V)
      (fun _ _ => rfl) A
    have ha : fixedCodim σ A ≤ rank A := hA.2
    have hr : 24 ≤ rank A := by omega
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr).trans
      (hA.1.card_eq_two_pow_rank ▸ Nat.card_le_card_of_injective A.subtype A.subtype_injective)
  have hclass := (adequateAlternative_knownSimple σ
    ⟨inferInstance,hfaith,hcore,hgen,⟨cover⟩⟩).of_ff σ hff
  cases hclass with
  | quasisimple hq c =>
    let : IsQuasisimple (generalizedFitting D) := hq
    let : IsSimpleGroup ((generalizedFitting D) ⧸ center (generalizedFitting D)) := IsQuasisimple.simple
    let : Nontrivial (generalizedFitting D) :=
      (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
    have hK : generalizedFitting D ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
    obtain ⟨F,hF,he⟩ := quasisimple_double_of_large_moved_sections σ _ c (hno _) (hdim _ hK)
    exact Or.inr ⟨c,F,hF,he⟩
  | symmetricThree c =>
    rw [Nat.card_congr c.equiv.toEquiv] at hcard
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm] at hcard
  | twoFactors c => exact Or.inl ⟨c⟩
  | outerSixThree c =>
    have hi : (c.first ⊔ c.second).index ≤ 2 :=
      Nat.le_of_dvd (by decide) (c.factors_index_dvd_two σ hgen)
    have hp : Nat.card (c.first ⊔ c.second : Subgroup D) = 1080 := by
      rw [←Nat.card_congr c.product.toEquiv,Nat.card_prod,
        Nat.card_congr c.firstEquiv.toEquiv,Nat.card_congr c.secondEquiv.toEquiv]
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hb := (c.first ⊔ c.second).index_mul_card
    rw [hp] at hb
    omega
  | hyperplane c =>
    have hK : c.first ≠ ⊥ := by
      intro he
      have hh := c.firstDimension
      have hz : moved σ c.first = ⊥ := by
        apply (subspaceCommutator_eq_bot_iff σ ⊤ c.first).mpr
        intro v _ a
        have ha : (a : D) = 1 := he.le a.property
        change σ (a : D) v = v
        rw [ha,map_one,Module.End.one_apply]
      rw [hz,finrank_bot] at hh
      omega
    have hh := hdim c.first hK
    change 24 ≤ Module.finrank (ZMod 2) (moved σ c.first) at hh
    rw [c.firstDimension] at hh
    omega

end CFSG.Quasithin.ChapterB.SourceInduction

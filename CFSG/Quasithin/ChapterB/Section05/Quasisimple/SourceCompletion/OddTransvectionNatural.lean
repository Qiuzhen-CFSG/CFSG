module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.SymmetricSix

/-!
# An odd transvection recognizes the natural symmetric-six section

An odd involution with fixed codimension one is a best offender. Its normal
closure contains the alternating group and an odd permutation, so the best
 offender subgroup is the whole symmetric group. The established B.5.1
classification then gives the natural six-letter moved section, with its
actual possibly outer group marking. For a fully moved action this supplies
a surjection whose kernel is the literal alternating fixed space.

This is the representation input in the last paragraph of MS93 (5.12),
printed p.927: the opposite critical seed acts as a transvection on the
actual forward-span quotient. The source quotient and fixed-index producer
are separate from this recognition theorem.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
local notation "S6" => Equiv.Perm (Fin 6)
local notation "A6" => alternatingGroup (Fin 6)

private theorem rank_one_codim_one_best
    (ρ : Representation (ZMod 2) S6 V)
    (A : Subgroup S6) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2) (hc : fixedCodim ρ A = 1) : IsBestOffender ρ A := by
  have hne : A ≠ ⊥ := by intro he; rw [he,card_bot] at hA; omega
  have hr : rank A = 1 := by simp only [rank,hA]; decide
  have hd := fixedCodim_add_finrank ρ A
  refine ⟨⟨hne,inferInstance⟩,fun B hBA => ?_⟩
  by_cases he : B = A
  · exact he ▸ le_rfl
  have hbcard : Nat.card B < 2 := by
    have hb := Nat.card_le_card_of_injective (inclusion hBA) (inclusion_injective hBA)
    have hn : Nat.card B ≠ Nat.card A := fun hh => he (eq_of_le_of_card_ge hBA hh.ge)
    omega
  have hB : B = ⊥ := eq_bot_of_card_le B (by omega)
  rw [hB,weight_bot]
  unfold weight
  omega

private theorem offenderSubgroup_eq_top_of_odd_transvection
    (ρ : Representation (ZMod 2) S6 V) (_hf : Function.Injective ρ)
    (A : Subgroup S6) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2) (hc : fixedCodim ρ A = 1) (hodd : ¬ A ≤ A6) :
    offenderSubgroup ρ = ⊤ := by
  have hbest := rank_one_codim_one_best ρ A hA hc
  have hAJ := hbest.le_offenderSubgroup ρ
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  have hJ : J ≠ ⊥ := fun he => hbest.1.1 (bot_unique (he ▸ hAJ))
  have hAlt : A6 ≤ J := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6)
    (by simp) ((nontrivial_iff_ne_bot J).mpr hJ)
  have hd : J.index ∣ 2 := (alternatingGroup.index_eq_two (α := Fin 6)) ▸ index_dvd_of_le hAlt
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact index_eq_one.mp h1
  · exact (hodd ((Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2) ▸ hAJ)).elim

private theorem alternatingSix_quasisimple : IsQuasisimple A6 where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

private theorem symmetricSix_source_conclusion_of_odd_transvection
    (ρ : Representation (ZMod 2) S6 V) (hf : Function.Injective ρ)
    (hsq : IsSQTK KnownSimple.IsKnownSimple A6)
    (A : Subgroup S6) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2) (hc : fixedCodim ρ A = 1) (hodd : ¬ A ≤ A6) :
    Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ A6) := by
  let := alternatingSix_quasisimple
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  have hC := GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 6 (by decide)
  have hfit : generalizedFitting S6 = A6 := generalizedFitting_eq_of_quasisimple_centralizer A6 hC
  have hcore : pCore 2 S6 = ⊥ := SimpleSocle.pCore_eq_bot (SimpleSocle.radical_eq_bot A6 hC) 2
  have hh : QuasisimpleSourceHypothesis ρ KnownSimple.IsKnownSimple A6 := by
    refine ⟨inferInstance,hf,inferInstance,hsq,?_,hcore,
      offenderSubgroup_eq_top_of_odd_transvection ρ hf A hA hc hodd⟩
    rw [hfit]
    exact (sup_eq_left.mpr (by
      rw [←hfit]
      exact (show center S6 ≤ fittingSubgroup S6 from le_sSup ⟨inferInstance,inferInstance⟩).trans
        (fitting_le_generalizedFitting S6))).symm
  exact knownSimple_quasisimpleClassificationInput
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    SourceClassification.irreducibleClassification_knownSimple
    SourceInduction.nonbinaryG2RootPairInput S6 V ρ A6 hh

private theorem alternatingSix_ne_top : A6 ≠ ⊤ := by
  intro he
  have hi := alternatingGroup.index_eq_two (α := Fin 6)
  rw [he,index_top] at hi
  omega

private theorem outerNatural_symmetricSix
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) S6 U) (ho : OuterNaturalAction σ) :
    IsSymmetricNatural σ 6 := by
  rcases ho with hn | hg
  · obtain ⟨n,hn5,hn8,⟨e⟩⟩ := hn
    have hc := Nat.card_congr e.groupEquiv.toEquiv
    rw [Nat.card_perm,Nat.card_perm] at hc
    simp only [Nat.card_fin] at hc
    interval_cases n <;> norm_num [Nat.factorial] at hc
    exact ⟨e⟩
  · obtain ⟨e⟩ := hg
    have hc := Nat.card_congr e.groupEquiv.toEquiv
    rw [Nat.card_perm,Atlas.G2.card_Model] at hc
    norm_num [Nat.factorial] at hc

theorem symmetricSix_moved_section_natural_of_odd_transvection
    (ρ : Representation (ZMod 2) S6 V) (hf : Function.Injective ρ)
    (hsq : IsSQTK KnownSimple.IsKnownSimple A6)
    (A : Subgroup S6) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2) (hc : fixedCodim ρ A = 1) (hodd : ¬ A ≤ A6) :
    ∃ s : MovedSection ρ A6, IsSymmetricNatural s.action 6 := by
  obtain ⟨c⟩ := symmetricSix_source_conclusion_of_odd_transvection ρ hf hsq A hA hc hodd
  refine ⟨c.sectionData,?_⟩
  cases c.clause_one with
  | irreducible _ _ _ _ ext =>
    exact outerNatural_symmetricSix _ (ext.resolve_left alternatingSix_ne_top).2
  | doubleThree _ whole _ _ _ => exact (alternatingSix_ne_top whole).elim
  | naturalDual _ _ whole _ => exact (alternatingSix_ne_top whole).elim
  | repeatedNatural _ _ _ _ _ whole _ => exact (alternatingSix_ne_top whole).elim

theorem symmetricSix_natural_quotient_of_odd_transvection
    (ρ : Representation (ZMod 2) S6 V) (hf : Function.Injective ρ)
    (hsq : IsSQTK KnownSimple.IsKnownSimple A6)
    (A : Subgroup S6) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2) (hc : fixedCodim ρ A = 1) (hodd : ¬ A ≤ A6)
    (hm : subspaceCommutator ρ ⊤ A6 = ⊤) :
    ∃ (e : S6 ≃* S6) (p : V →ₗ[ZMod 2] BinaryPermutation.natural (Fin 6)),
      Function.Surjective p ∧ p.ker = fixedSpace ρ A6 ∧
      ∀ g v, p (ρ g v) = BinaryPermutation.naturalRepresentation (Fin 6) (e g) (p v) := by
  obtain ⟨s,⟨e⟩⟩ := symmetricSix_moved_section_natural_of_odd_transvection ρ hf hsq A hA hc hodd
  have hs : s.space.toSubmodule = ⊤ := s.space_eq.trans hm
  let i := (LinearEquiv.ofTop s.space.toSubmodule hs).symm
  let p : V →ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    e.linearEquiv.toLinearMap.comp (s.central.toSubmodule.mkQ.comp i.toLinearMap)
  have hi (g : S6) (v : V) : i (ρ g v) = s.space.toRepresentation g (i v) := by
    apply Subtype.ext
    rfl
  refine ⟨e.groupEquiv,p,?_,?_,?_⟩
  · exact e.linearEquiv.surjective.comp (s.central.toSubmodule.mkQ_surjective.comp i.surjective)
  · ext v
    change e.linearEquiv (s.central.toSubmodule.mkQ (i v)) = 0 ↔ v ∈ fixedSpace ρ A6
    rw [e.linearEquiv.map_eq_zero_iff,←LinearMap.mem_ker,Submodule.ker_mkQ,s.central_eq]
    change (∀ g : A6, s.space.toRepresentation g (i v) = i v) ↔ ∀ g : A6, ρ g v = v
    constructor
    · intro hv g
      apply i.injective
      rw [hi]
      exact hv g
    · intro hv g
      rw [←hi,hv g]
  · intro g v
    change e.linearEquiv (s.central.toSubmodule.mkQ (i (ρ g v))) = _
    rw [hi,←s.central.quotientRepresentation_mk]
    exact e.intertwines g _

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion

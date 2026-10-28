module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.LiteralMovedCover
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SymplecticCoverTransport
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2CoverTransport
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots.Binary
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# The nonsplit natural rows in the tensor point-centralizer argument

A nonzero component-fixed vector in the actual moved module invokes clause
(2) of the source B.5.1 conclusion. A proper full-Sylow local component with
alternating-five two-core quotient excludes the rank-one and alternating
rows. Its order-five section excludes the binary linear-three and G₂ rows;
perfectness excludes the full binary symplectic group. Only the nonbinary
natural symplectic and G₂ actions remain, on the original central quotient.

The resulting cover is the literal moved-section projection. The local
fixed-space calculations for those two covers supply the contradiction in
the point-centralizer argument without using Chapter 10 point inspection.

Source: Aschbacher--Smith, Proposition 9.4.1, printed p.735/PDF p.752,
using B.5.1(2), printed pp.99--103 (combined 1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceA5TensorExclusion
open ChapterB.QuasisimpleSource
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open ChapterA.Section03.SourceEmbeddings.FiveLocalFF

private theorem five_dvd_card_of_local_section {C : Type*} [Group C] [Finite C]
    (B : Subgroup C) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    5 ∣ Nat.card C := by
  have hd := card_quotient_dvd_card (pCore 2 B)
  rw [Nat.card_congr eB.toEquiv, nat_card_alternatingGroup] at hd
  norm_num at hd
  exact (by decide : 5 ∣ 60).trans (hd.trans B.card_subgroup_dvd_card)

private theorem rank_one_excluded {C : Type*} [Group C] [Finite C] [IsQuasisimple C]
    (R : Sylow 2 C) (B : Subgroup C) (hB : B ∈ localCComponents R)
    (hp : B ≠ ⊤) (F : BinaryField) (e : C ≃* SL(2,F.Carrier)) : False := by
  have ht : (⊤ : Subgroup C).IsCComponent :=
    (show IsComponent C ⊤ from ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  exact hp (eq_of_solvable_sylow_overgroups R hB ht le_top
    (SolvableSylowOvergroups.of_equiv (topEquiv.trans e)
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup))

private theorem symplectic_degree_gt_one {C : Type*} [Group C] [IsQuasisimple C]
    (F : BinaryField) (e : C ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) :
    1 < F.degree := by
  by_contra hn
  have hdeg : F.degree = 1 := by have := F.degree_pos; omega
  have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq, hdeg]; norm_num
  let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) F.Carrier) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply SymplecticFourOrthogonalCover.Roots.card_two_root_not_mem_derived hc
  rw [Group.IsPerfect.commutator_eq_top]
  trivial

/-- The literal local A₅ section reduces the nonsplit source list to the
two nonbinary natural-cover models. -/
theorem nonsplit_five_local_models
    {C W : Type*} [Group C] [Finite C] [IsQuasisimple C]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) C W) (hn : NonsplitNatural σ)
    (R : Sylow 2 C) (B : Subgroup C) (hB : B ∈ localCComponents R)
    (hp : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    (∃ F : BinaryField, 1 < F.degree ∧ Nonempty (ActionEquiv σ (binarySymplectic F))) ∨
    (∃ F : BinaryField, 1 < F.degree ∧ Nonempty (ActionEquiv σ (binaryG2 F))) := by
  have h5 := five_dvd_card_of_local_section B eB
  cases hn with
  | linearTwo F a => exact (rank_one_excluded R B hB hp F a.some.groupEquiv).elim
  | symplectic F a =>
    exact Or.inl ⟨F, symplectic_degree_gt_one F a.some.groupEquiv, a⟩
  | g2 F a =>
    refine Or.inr ⟨F, ?_, a⟩
    by_contra hh
    have hd : F.degree = 1 := by have := F.degree_pos; omega
    have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq, hd]; norm_num
    rw [Nat.card_congr a.some.groupEquiv.toEquiv, Atlas.G2.card_Model, hc] at h5
    norm_num at h5
  | alternatingSix a =>
    exact (AlternatingSmall.not_proper_six R B hB hp a.some.groupEquiv).elim
  | alternatingEight a =>
    exact (AlternatingSmall.not_section_eight R B hB eB a.some.groupEquiv).elim
  | derivedG2 a =>
    rw [Nat.card_congr a.some.groupEquiv.toEquiv,
      Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at h5
    norm_num at h5
  | linearThree a =>
    rw [Nat.card_congr a.some.groupEquiv.toEquiv] at h5
    change 5 ∣ Nat.card (SL(3,ZMod 2)) at h5
    rw [Matrix.PSL3Two.card_SL] at h5
    norm_num at h5

/-- Clause (2) of the full source theorem supplies Irr⁺ and natural-model
coordinates on the same moved quotient when its moved and fixed spaces do
not complement one another. -/
theorem source_nonsplit_five_local_models
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [IsQuasisimple C]
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hn : ¬ IsCompl h.sectionData.space.toSubmodule (fixedSpace ρ C))
    (R : Sylow 2 C) (B : Subgroup C) (hB : B ∈ localCComponents R)
    (hp : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    IsIrrPlus ρ C h.sectionData.space.toSubmodule ∧
      ((∃ F : BinaryField, 1 < F.degree ∧
          Nonempty (ActionEquiv (h.sectionData.action.comp C.subtype) (binarySymplectic F))) ∨
       (∃ F : BinaryField, 1 < F.degree ∧
          Nonempty (ActionEquiv (h.sectionData.action.comp C.subtype) (binaryG2 F)))) := by
  obtain ⟨hi, hm⟩ := h.clause_two hn
  exact ⟨hi, nonsplit_five_local_models _ hm R B hB hp eB⟩

/-- The source natural-cover alternatives exclude every nonzero globally
fixed vector from a fully moved local subspace centralized by its two-core.
The quotient, projection and subspace all remain the literal source objects. -/
theorem source_five_local_moved_disjoint
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [IsQuasisimple C]
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (R : Sylow 2 C) (B : Subgroup C) (hB : B ∈ localCComponents R)
    (hp : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (A : Submodule (ZMod 2) V) (hA : A ≤ moved ρ C)
    (hcore : A ≤ fixedSpace (ρ.comp C.subtype) (B.pCoreIn 2))
    (hm : subspaceCommutator (ρ.comp C.subtype) A B = A) :
    Disjoint A (fixedSpace ρ C) := by
  have hspace : A ≤ h.sectionData.space.toSubmodule := by
    simpa only [h.sectionData.space_eq] using hA
  by_cases hc : IsCompl h.sectionData.space.toSubmodule (fixedSpace ρ C)
  · exact hc.disjoint.mono_left hspace
  obtain ⟨hi, hmodels⟩ := source_nonsplit_five_local_models ρ C h hc R B hB hp eB
  have hd : Disjoint (A.comap h.sectionData.space.toSubmodule.subtype)
      (Representation.OneCohomology.fixed
        (h.sectionData.space.toRepresentation.comp C.subtype)) := by
    rcases hmodels with ⟨F,hF,⟨e⟩⟩ | ⟨F,hF,⟨e⟩⟩
    · exact symplectic_five_section_original_cover_moved_disjoint F.card_eq hF
        e.groupEquiv e.linearEquiv e.intertwines R B hB hp eB
        h.sectionData.literalCoverProjection (h.sectionData.literalCoverProjection_isCover hi)
        (A.comap h.sectionData.space.toSubmodule.subtype)
        (h.sectionData.comap_le_fixedSpace A (B.pCoreIn 2) hcore)
        (h.sectionData.subspaceCommutator_comap A hA B hm)
    · exact G2.five_section_original_cover_moved_disjoint F.card_eq hF
        e.groupEquiv e.linearEquiv e.intertwines R B hB hp eB
        h.sectionData.literalCoverProjection (h.sectionData.literalCoverProjection_isCover hi)
        (A.comap h.sectionData.space.toSubmodule.subtype)
        (h.sectionData.comap_le_fixedSpace A (B.pCoreIn 2) hcore)
        (h.sectionData.subspaceCommutator_comap A hA B hm)
  rw [Submodule.disjoint_def]
  intro v hv hfix
  have he : (⟨v,hspace hv⟩ : h.sectionData.space.toSubmodule) = 0 :=
    Submodule.disjoint_def.mp hd _ hv (fun c => Subtype.ext (hfix c))
  exact congrArg Subtype.val he

/-- The central point used in 9.4.1 is zero under the original nonsplit
local-subspace hypotheses. No further model or cohomology premise remains. -/
theorem source_five_local_moved_fixed_eq_zero
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [IsQuasisimple C]
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (R : Sylow 2 C) (B : Subgroup C) (hB : B ∈ localCComponents R)
    (hp : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (A : Submodule (ZMod 2) V) (hA : A ≤ moved ρ C)
    (hcore : A ≤ fixedSpace (ρ.comp C.subtype) (B.pCoreIn 2))
    (hm : subspaceCommutator (ρ.comp C.subtype) A B = A)
    (v : V) (hv : v ∈ A) (hfix : v ∈ fixedSpace ρ C) : v = 0 :=
  Submodule.disjoint_def.mp
    (source_five_local_moved_disjoint ρ C h R B hB hp eB A hA hcore hm) v hv hfix

end CFSG.Quasithin.Chapter10.SourceA5TensorExclusion

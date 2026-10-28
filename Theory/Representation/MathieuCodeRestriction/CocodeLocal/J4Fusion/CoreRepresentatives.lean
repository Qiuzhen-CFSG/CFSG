module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.SextetCore
public import Theory.Mathieu.M24.LocalGeometry.SextetCore
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions

/-!
# Both native involution classes in a sextet two-core

Two generators of the existing certified elementary Sylow subgroup have
eight and zero fixed points. The proved native involution coverage identifies
their classes. The original coordinate transporter places both in the standard
sextet core, and sextet transitivity carries them to any marked sextet.
This supplies the quotient representatives in AS91 (6.4), printed p.602.
-/

public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open M24ChapterHStabilizers M24InvolutionCentralizers
open MathieuCode.SextetLayers.CoordinateTransport
open scoped Pointwise
namespace MathieuCode.J4Fusion
noncomputable section

private def candidateRepresentative (b : Bool) : M24 :=
  EvenCandidates.generator 1 (if b then 0 else 3)

private lemma candidateRepresentative_order (b : Bool) :
    orderOf (candidateRepresentative b) = 2 := by
  apply orderOf_eq_prime (EvenCandidates.generator_square 1 _)
  intro he
  have hh := congrArg (fun g : M24 => g.val 0) he
  change (EvenCandidates.generator 1 _).val 0 = 0 at hh
  rw [EvenCandidates.generator_apply] at hh
  have hn : ∀ b : Bool, EvenCandidates.generatorPoint 1 (if b then 0 else 3) 0 ≠ 0 := by
    decide +kernel
  exact hn b hh

private lemma candidateRepresentative_fixed (b : Bool) :
    (fixedPoints (candidateRepresentative b)).card = if b then 8 else 0 := by
  have he : fixedPoints (candidateRepresentative b) =
      Finset.univ.filter (fun x => EvenCandidates.generatorPoint 1 (if b then 0 else 3) x = x) := by
    ext x
    simp only [mem_fixedPoints,Finset.mem_filter,Finset.mem_univ,true_and]
    change (EvenCandidates.generator 1 _).val x = x ↔ _
    rw [EvenCandidates.generator_apply]
  rw [he]
  cases b <;> decide +kernel

private lemma candidateRepresentative_class (b : Bool) :
    IsConj (if b then involution2A else involution2B) (candidateRepresentative b) := by
  rcases involution_classes _ (candidateRepresentative_order b) with ha | hb
  · cases b
    · have hh := m24Blocks_card _ (class2A_fixed_octad ha)
      rw [candidateRepresentative_fixed] at hh
      contradiction
    · exact ha
  · cases b
    · exact hb
    · have hh := congrArg Finset.card (class2B_fixed_empty hb)
      rw [candidateRepresentative_fixed] at hh
      contradiction

lemma standard_core_class (b : Bool) :
    ∃ s ∈ SextetCore.core, IsConj (if b then involution2A else involution2B) s := by
  refine ⟨MulAut.conj SextetCore.transport (candidateRepresentative b),?_,
    (candidateRepresentative_class b).trans (isConj_iff.mpr ⟨SextetCore.transport,rfl⟩)⟩
  rw [←SextetCore.candidate_conjugate_core]
  exact ⟨candidateRepresentative b,EvenCandidates.generator_mem 1 _,rfl⟩

lemma sextet_core_class (S : Sextet) (b : Bool) :
    ∃ s ∈ (sextetStabilizer S).pCoreIn 2,
      IsConj (if b then involution2A else involution2B) s := by
  obtain ⟨g,hg⟩ := exists_sextet_conjugator S
  have hm : (sextetStabilizer standardSextet).map (MulAut.conj g).toMonoidHom =
      sextetStabilizer S := by
    change (MulAction.stabilizer M24 standardSextet.parts).map _ =
      MulAction.stabilizer M24 S.parts
    rw [←MulAction.stabilizer_smul_eq_stabilizer_map_conj,hg]
  obtain ⟨s,hs,hc⟩ := standard_core_class b
  refine ⟨MulAut.conj g s,?_,hc.trans (isConj_iff.mpr ⟨g,rfl⟩)⟩
  rw [←hm,←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  exact ⟨s,hs,rfl⟩

end
end MathieuCode.J4Fusion

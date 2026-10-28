module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper.Transport
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.Reduction
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry

/-!
# The strong actor determines the original parabolic marking

The actual index-three overgroup of the marked Sylow subgroup is one of
the two flag parabolics. A strong offender inside its relative two-core
excludes the point parabolic: that core does not contain the transvection
(01). Thus the original parabolic, rather than a replacement subgroup of
the same abstract type, maps to the syntheme stabilizer H2.

Source: Aschbacher–Smith B.3.4(2)(i), used in 13.8.26, printed p.962.
The index-three and two-core placement are the earlier field and critical
geometry inputs; no upper-module quotient is assumed in this step.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper
open NaturalSix

private theorem sylow_flag : ChapterB.Offenders.Six.sylowCarrier = H1 ⊓ H2 := by
  apply Subgroup.eq_of_le_of_card_ge
  · apply le_inf ?_ Marked.sylow_le_H2
    intro g hg
    obtain ⟨i, rfl⟩ := (ChapterB.Offenders.Six.mem_sylowCarrier_iff g).mp hg
    clear hg
    revert i
    decide +kernel
  · rw [ChapterB.Offenders.Six.card_sylowCarrier]
    have he : (H1 ⊓ H2).map (MulAut.conj flagRelabel).toMonoidHom = borel := by
      rw [map_inf _ _ _ (MulAut.conj flagRelabel).injective, flagRelabel_syntheme]
      change (MulAction.stabilizer S (pair 4 5)).map _ ⊓ H2 = borel
      rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
      rfl
    have hc := congrArg (fun Q : Subgroup S => Nat.card Q) he
    rw [card_map_of_injective (MulAut.conj flagRelabel).injective, borel_order] at hc
    exact hc.le

private theorem parabolic_alternatives (P : Subgroup S)
    (hT : ChapterB.Offenders.Six.sylowCarrier ≤ P)
    (hi : ChapterB.Offenders.Six.sylowCarrier.relIndex P = 3) :
    P = H1 ∨ P = H2 := by
  let e := MulAut.conj flagRelabel
  have hinv : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S := by
    apply MonoidHom.ext
    intro x
    exact e.apply_symm_apply x
  have hcancel (Q : Subgroup S) : (Q.map e.symm.toMonoidHom).map e.toMonoidHom = Q := by
    rw [map_map, hinv, map_id]
  have he : borel.map e.toMonoidHom = H1 ⊓ H2 := by
    rw [borel, map_inf _ _ _ e.injective, flagRelabel_duad]
    change H1 ⊓ H2.map (MulAut.conj flagRelabel).toMonoidHom = _
    rw [flagRelabel_syntheme]
  have hb : borel ≤ P.map e.symm.toMonoidHom := by
    rw [← sylow_flag] at he
    intro b hb
    apply mem_map_equiv.mpr
    simpa only [MulEquiv.symm_symm] using hT (he ▸ mem_map_of_mem e.toMonoidHom hb)
  have hi' : borel.relIndex (P.map e.symm.toMonoidHom) = 3 := by
    have hh := relIndex_map_map_of_injective (f := e.toMonoidHom)
      borel (P.map e.symm.toMonoidHom) e.injective
    rw [he, ← sylow_flag, hcancel] at hh
    exact hh.symm.trans hi
  rcases ResidualPairRecognition.index_three_over_borel _ hb hi' with hd | hs
  · left
    have hh := congrArg (fun Q : Subgroup S => Q.map e.toMonoidHom) hd
    rw [hcancel, show duadStabilizer.map e.toMonoidHom = H1 from flagRelabel_duad] at hh
    exact hh
  · right
    have hh := congrArg (fun Q : Subgroup S => Q.map e.toMonoidHom) hs
    rw [hcancel, show synthemeStabilizer.map e.toMonoidHom = H2 from flagRelabel_syntheme] at hh
    exact hh

private theorem swap01_not_mem_pointCore : swap01 ∉ H1.pCoreIn 2 := by
  rw [H1_core_eq_pointCore]
  rintro ⟨x, hx, he⟩
  have hc : ∀ x : DuadProduct, x ∈ DuadCalculation.productCore →
      (MulAut.conj flagRelabel) (duadProductHom x) ≠ swap01 := by
    simp only [DuadCalculation.productCore, mem_prod, mem_top, true_and,
      DuadCalculation.core_mem_iff]
    decide +kernel
  exact hc x hx he

/-- The actual parabolic is the plane parabolic once its two-core contains
the strong natural actor. The hypotheses retain relative two-core conventions. -/
theorem parabolic_eq_plane (P : Subgroup S)
    (hT : ChapterB.Offenders.Six.sylowCarrier ≤ P)
    (hi : ChapterB.Offenders.Six.sylowCarrier.relIndex P = 3)
    (hD : D ≤ P.pCoreIn 2) : P = H2 := by
  rcases parabolic_alternatives P hT hi with rfl | h
  · exact (swap01_not_mem_pointCore (hD swap01_mem_D)).elim
  · exact h

/-- The relative two-core lies in the prescribed ambient Sylow subgroup
whenever the parabolic contains that Sylow. -/
theorem core_le_sylow (P : Subgroup S)
    (hT : ChapterB.Offenders.Six.sylowCarrier ≤ P) :
    P.pCoreIn 2 ≤ ChapterB.Offenders.Six.sylowCarrier := by
  have hh := pCoreIn_le_sylow P (ChapterB.Offenders.Six.sylow.subtype hT)
  change P.pCoreIn 2 ≤ (ChapterB.Offenders.Six.sylowCarrier.subgroupOf P).map P.subtype at hh
  rwa [map_subgroupOf_eq_of_le hT] at hh

variable {J E : Type*} [Group J] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] {σ : Representation (ZMod 2) J E}

/-- Applying B.3.4 to a lower constituent identifies the same source
parabolic after the specified γ-to-α conjugation. -/
theorem parabolic_marking (m : NaturalSection σ) (T P A B : Subgroup J) (h : J)
    (hTP : T ≤ P) (hi : T.relIndex P = 3)
    (hT : T.map m.actor = ChapterB.Offenders.Six.sylowCarrier)
    (hcore : A.map (MulAut.conj h).toMonoidHom ≤ P.pCoreIn 2)
    (hBA : B ≤ A) (hB : IsStrongOffender σ B) : P.map m.actor = H2 := by
  have hcube := (m.conjugateMarking h).strong_image_eq_cube hBA hB (by
    rw [m.conjugateMarking_actor_map]
    have hc : (P.pCoreIn 2).map m.actor ≤ ChapterB.Offenders.Six.sylowCarrier := by
      rw [map_pCoreIn_of_injective 2 P m.actor m.injective]
      exact core_le_sylow _ (hT ▸ map_mono hTP)
    exact (map_mono hcore).trans hc)
  apply parabolic_eq_plane
  · rw [← hT]
    exact map_mono hTP
  · rw [← hT, relIndex_map_map_of_injective _ _ m.injective]
    exact hi
  · rw [← map_pCoreIn_of_injective 2 P m.actor m.injective, ← hcube,
      m.conjugateMarking_actor_map]
    exact map_mono ((map_mono hBA).trans hcore)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper
end

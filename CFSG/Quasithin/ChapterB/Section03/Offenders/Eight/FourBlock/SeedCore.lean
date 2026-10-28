module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.FourBlock
public import Theory.Representation.BinaryPermutation.AlternatingEightNaturalFixedLine
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PCoreImage
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Seed cores for the six-dimensional A₈ module

A nonzero Sylow-fixed seed is a line. Its stabilizer in any group between
A₈ and S₈ has two-core contained, after the same conjugation, in the
four-block Klein radical. That radical has no offenders.

Source application: Aschbacher--Smith 15.1.28, printed p.1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open BinaryPermutation
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction
namespace CFSG.Quasithin.ChapterB.Offenders.Eight.FourBlock

private theorem intermediate_normal {H : Subgroup S8} (hH : alternatingGroup (Fin 8) ≤ H) :
    H.Normal := by
  have hi := index_dvd_of_le hH
  rw [alternatingGroup.index_eq_two] at hi
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hi with hi | hi
  · exact normal_of_index_eq_one hi
  · exact normal_of_index_eq_two hi

/-- The literal core of any intermediate point stabilizer is contained in the
four-block radical after the same conjugation. -/
theorem point_core_le (H : Subgroup S8) (hH : alternatingGroup (Fin 8) ≤ H)
    (Q : Sylow 2 (alternatingGroup (Fin 8))) (v : natural (Fin 8)) (hv : v ≠ 0)
    (hf : v ∈ fixedSpace (alternatingNaturalRepresentation (Fin 8)) Q) :
    ∃ r : alternatingGroup (Fin 8),
      ((subspaceKernel (naturalRepresentation (Fin 8)) (Submodule.span (ZMod 2) {v}) H).pCoreIn 2).map
        (MulAut.conj r.val).toMonoidHom ≤ kleinGroup := by
  obtain ⟨r,hr⟩ := TerminalOrthogonal.Eight.alternating_exists_conjugate_stabilizer Q v hv
    (fun g hg => hf ⟨g,hg⟩)
  refine ⟨r,?_⟩
  let f := (MulAut.conj r.val).toMonoidHom
  have hm : (subspaceKernel (naturalRepresentation (Fin 8)) (Submodule.span (ZMod 2) {v}) H).map f =
      H ⊓ fourStabilizer := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      have hna : f a ∈ H := (intermediate_normal hH).conj_mem a ha.1 r.val
      exact ⟨hna,(hr a).mp (ha.2 v (Submodule.subset_span (by simp)))⟩
    · intro hx
      let a := r.val⁻¹ * x * r.val
      have hea : f a = x := by dsimp [f,a]; group
      refine ⟨a,⟨(intermediate_normal hH).conj_mem x hx.1 r.val⁻¹,?_⟩,hea⟩
      have hfix : naturalRepresentation (Fin 8) a v = v := (hr a).mpr (show f a ∈ fourStabilizer from hea.symm ▸ hx.2)
      intro w hw
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul,hfix]
  rw [map_pCoreIn_of_injective 2 _ f (MulAut.conj r.val).injective,hm]
  rw [← fourStabilizer_pCoreIn]
  apply pCoreIn_mono_of_normalizes inf_le_right
  apply le_normalizer_iff.mpr
  intro g hg n hn
  exact ⟨(intermediate_normal hH).conj_mem n hn.1 g,
    fourStabilizer.mul_mem (fourStabilizer.mul_mem hg hn.2) (fourStabilizer.inv_mem hg)⟩

/-- A nonzero alternating-Sylow-fixed seed admits no offender in the intrinsic
core of its stabilizer, also inside the full symmetric extension. -/
theorem no_seed_core_offender (H : Subgroup S8) (hH : alternatingGroup (Fin 8) ≤ H)
    (Q : Sylow 2 (alternatingGroup (Fin 8))) (P : Submodule (ZMod 2) (natural (Fin 8)))
    (hn : P ≠ ⊥) (hf : P ≤ fixedSpace (alternatingNaturalRepresentation (Fin 8)) Q)
    {A : Subgroup S8} (hA : IsOffender (naturalRepresentation (Fin 8)) A)
    (hcore : A ≤ (subspaceKernel (naturalRepresentation (Fin 8)) P H).pCoreIn 2) : False := by
  obtain ⟨v,hv,hvn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have heq : P = Submodule.span (ZMod 2) {v} := by
    apply le_antisymm
    · intro w hw
      rcases alternatingEight_sylow_fixed_unique Q v w hvn (hf hv) (hf hw) with rfl | rfl
      · exact Submodule.zero_mem _
      · exact Submodule.subset_span (by simp)
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv)
  obtain ⟨r,hr⟩ := point_core_le H hH Q v hvn (hf hv)
  rw [← heq] at hr
  have hAK := (map_mono (f := (MulAut.conj r.val).toMonoidHom) hcore).trans hr
  apply no_offender hAK
  exact (show IsConjugateTo (A.map (MulAut.conj r.val).toMonoidHom) A from ⟨r.val,rfl⟩).isOffender _ hA
end CFSG.Quasithin.ChapterB.Offenders.Eight.FourBlock

module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Models
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Transport of the actual middle parabolic between projective coordinates

Every automorphism of GL₄(2) is inner or inverse transpose followed by an
inner automorphism. Linear images transport flag stabilizers under inner
automorphisms. The dot-product annihilator transports them under inverse
transpose, reverses inclusions, and exchanges dimensions one and three.
Thus a flag of types {1,3} remains of those types under every automorphism.

Comparing two component isomorphisms through their actual linear actions
then transports the flag while preserving its ambient stabilizer exactly.
This supplies the marking needed to apply the natural-module exclusions
to coordinates obtained independently from a classification theorem.

Source: Aschbacher–Smith, 15.3.28(3) and the proof of 15.3.32(1), combined
manuscript (1 March 2004), printed pp.1131–1132; the binary automorphism
theorem is proved in `BinaryLinear.OuterCyclic` from GLS3, Theorem 2.5.12.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
open Chapter2.ComponentRefinement.LieType.Binary

private noncomputable def perpendicular (W : Space 4) : Space 4 :=
  W.dualAnnihilator.comap (dotProductEquiv (ZMod 2) (Fin 4)).toLinearMap

private theorem mem_perpendicular (W : Space 4) (v : Vector 4) :
    v ∈ perpendicular W ↔ ∀ w ∈ W, dotProduct v w = 0 := by
  simp only [perpendicular, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
    LinearEquiv.coe_coe]
  rfl

private theorem perpendicular_finrank (W : Space 4) :
    Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) (perpendicular W) = 4 := by
  have he := (LinearEquiv.ofSubmodule' (dotProductEquiv (ZMod 2) (Fin 4))
    W.dualAnnihilator).finrank_eq
  change Module.finrank (ZMod 2) (perpendicular W) =
    Module.finrank (ZMod 2) W.dualAnnihilator at he
  rw [he]
  simpa only [Module.finrank_fin_fun] using Subspace.finrank_add_finrank_dualAnnihilator_eq W

private theorem perpendicular_anti {A H : Space 4} (hAH : A ≤ H) :
    perpendicular H ≤ perpendicular A := by
  intro v hv
  rw [mem_perpendicular] at hv ⊢
  intro w hw
  exact hv w (hAH hw)

private theorem perpendicular_perpendicular (W : Space 4) :
    perpendicular (perpendicular W) = W := by
  have hle : W ≤ perpendicular (perpendicular W) := by
    intro w hw
    rw [mem_perpendicular]
    intro v hv
    rw [dotProduct_comm]
    exact (mem_perpendicular W v).mp hv w hw
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have h1 := perpendicular_finrank W
  have h2 := perpendicular_finrank (perpendicular W)
  omega

private theorem graph_mem_parabolic (g : BinaryLinear.GL (Vector 4)) (W : Space 4) :
    BinaryLinear.OuterCyclic.graphLinear 4 g ∈ BinaryLinear.parabolic (perpendicular W) ↔
      g ∈ BinaryLinear.parabolic W := by
  have forward (g : BinaryLinear.GL (Vector 4)) (W : Space 4)
      (hg : g ∈ BinaryLinear.parabolic W) :
      BinaryLinear.OuterCyclic.graphLinear 4 g ∈ BinaryLinear.parabolic (perpendicular W) := by
    intro v
    simp only [mem_perpendicular]
    constructor
    · intro hv w hw
      have hgw : g w ∈ W := (hg w).mpr hw
      simpa only [BinaryLinear.OuterCyclic.graphLinear_dotProduct] using hv (g w) hgw
    · intro hv w hw
      have hgw : g.symm w ∈ W := (hg (g.symm w)).mp (by simpa using hw)
      have he := BinaryLinear.OuterCyclic.graphLinear_dotProduct g v (g.symm w)
      rw [LinearEquiv.apply_symm_apply] at he
      exact he.trans (hv _ hgw)
  refine ⟨fun hg => ?_, forward g W⟩
  have hh := forward (BinaryLinear.OuterCyclic.graphLinear 4 g) (perpendicular W) hg
  rw [perpendicular_perpendicular] at hh
  have hi : BinaryLinear.OuterCyclic.graphLinear 4
      (BinaryLinear.OuterCyclic.graphLinear 4 g) = g :=
    congrArg (fun a : MulAut (BinaryLinear.GL (Vector 4)) => a g)
      (BinaryLinear.OuterCyclic.graphLinear_sq 4)
  rwa [hi] at hh

private noncomputable def pairFlag (A H : Space 4) (hAH : A ≤ H)
    (hA : Module.finrank (ZMod 2) A = 1) (hH : Module.finrank (ZMod 2) H = 3) : Flag 4 where
  spaces := {A, H}
  nonempty := ⟨A, by simp⟩
  proper W hW := by
    have hd : Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 3 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl
      · exact Or.inl hA
      · exact Or.inr hH
    constructor
    · intro he
      rw [he, finrank_bot] at hd
      omega
    · intro he
      rw [he, finrank_top, Module.finrank_fin_fun] at hd
      omega
  chain W hW W' hW' := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW hW'
    rcases hW with rfl | rfl <;> rcases hW' with rfl | rfl
    · exact Or.inl le_rfl
    · exact Or.inl hAH
    · exact Or.inr hAH
    · exact Or.inl le_rfl

private theorem pairFlag_types (A H : Space 4) (hAH : A ≤ H)
    (hA : Module.finrank (ZMod 2) A = 1) (hH : Module.finrank (ZMod 2) H = 3) :
    (pairFlag A H hAH hA hH).types = {1, 3} := by
  classical
  simp [Flag.types, pairFlag, hA, hH]

private theorem middleFlag_pair (F : Flag 4) (hF : F.types = {1, 3}) :
    ∃ A H : Space 4, F.spaces = {A, H} ∧
      Module.finrank (ZMod 2) A = 1 ∧ Module.finrank (ZMod 2) H = 3 ∧ A ≤ H := by
  classical
  obtain ⟨A, hm₁, hd₁⟩ := Finset.mem_image.mp (show 1 ∈ F.types by rw [hF]; simp)
  obtain ⟨H, hm₃, hd₃⟩ := Finset.mem_image.mp (show 3 ∈ F.types by rw [hF]; simp)
  have unique (W W' : Space 4) (hW : W ∈ F.spaces) (hW' : W' ∈ F.spaces)
      (hd : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) W') : W = W' := by
    rcases F.chain W hW W' hW' with hle | hle
    · exact Submodule.eq_of_le_of_finrank_eq hle hd
    · exact (Submodule.eq_of_le_of_finrank_eq hle hd.symm).symm
  refine ⟨A, H, ?_, hd₁, hd₃, ?_⟩
  · ext W
    constructor
    · intro hW
      have hd : Module.finrank (ZMod 2) W ∈ F.types := Finset.mem_image.mpr ⟨W, hW, rfl⟩
      rw [hF] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
      exact hd.elim (fun hd => Or.inl (unique W A hW hm₁ (hd.trans hd₁.symm)))
        (fun hd => Or.inr (unique W H hW hm₃ (hd.trans hd₃.symm)))
    · intro hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      exact hW.elim (fun h => h ▸ hm₁) (fun h => h ▸ hm₃)
  · rcases F.chain A hm₁ H hm₃ with hle | hle
    · exact hle
    · have hd := Submodule.finrank_mono hle
      omega

private theorem conjugate_mem_parabolic (b g : BinaryLinear.GL (Vector 4)) (W : Space 4) :
    MulAut.conj b g ∈ BinaryLinear.parabolic (W.map b.toLinearMap) ↔
      g ∈ BinaryLinear.parabolic W := by
  rw [← conjugate_parabolic, mem_map_equiv, MulEquiv.symm_apply_apply]

/-- Every automorphism of the actual four-dimensional binary linear group
transports a flag of types {1,3} to another such flag, together with its
stabilizer. Inverse transpose exchanges the two endpoints. -/
theorem exists_middleFlag_transport (a : MulAut (BinaryLinear.GL (Vector 4)))
    (F : Flag 4) (hF : F.types = {1, 3}) :
    ∃ F' : Flag 4, F'.types = {1, 3} ∧ ∀ g,
      (∀ W ∈ F'.spaces, a g ∈ BinaryLinear.parabolic W) ↔
        (∀ W ∈ F.spaces, g ∈ BinaryLinear.parabolic W) := by
  classical
  obtain ⟨A, H, hspaces, hA, hH, hAH⟩ := middleFlag_pair F hF
  obtain ⟨b, hb⟩ := BinaryLinear.OuterCyclic.inner_graph (Or.inl rfl) a
  let A' := A.map b.toLinearMap
  let H' := H.map b.toLinearMap
  have hAH' : A' ≤ H' := Submodule.map_mono hAH
  have hA' : Module.finrank (ZMod 2) A' = 1 := (b.finrank_map_eq A).trans hA
  have hH' : Module.finrank (ZMod 2) H' = 3 := (b.finrank_map_eq H).trans hH
  rcases hb with rfl | rfl
  · refine ⟨pairFlag A' H' hAH' hA' hH', pairFlag_types _ _ _ _ _, ?_⟩
    intro g
    simp only [pairFlag, hspaces, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq, A', H', conjugate_mem_parabolic]
  · have hA'' : Module.finrank (ZMod 2) (perpendicular H') = 1 := by
      have h := perpendicular_finrank H'
      rw [hH'] at h
      omega
    have hH'' : Module.finrank (ZMod 2) (perpendicular A') = 3 := by
      have h := perpendicular_finrank A'
      rw [hA'] at h
      omega
    refine ⟨pairFlag (perpendicular H') (perpendicular A')
      (perpendicular_anti hAH') hA'' hH'', pairFlag_types _ _ _ _ _, ?_⟩
    intro g
    simp only [pairFlag, hspaces, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq, MulAut.mul_apply, graph_mem_parabolic,
      A', H', conjugate_mem_parabolic, and_comm]

variable {K : Type*} [Group K] {L P : Subgroup K}

/-- A change of projective coordinates preserves the *actual* marked parabolic.
The flag is transported as well, rather than identified by its dimensions alone. -/
theorem exists_remarking (mark : Models.MiddleNodeMarking L P) (model : L ≃* PSL 4) :
    ∃ F : Flag 4, F.types = {1, 3} ∧ P = ambientFlagStabilizer model F := by
  let a := (linearModel mark.model).symm.trans (linearModel model)
  obtain ⟨F, hF, htransport⟩ := exists_middleFlag_transport a mark.flag mark.middle
  refine ⟨F, hF, ?_⟩
  rw [mark.parabolic]
  apply congrArg (fun Q : Subgroup L => Q.map L.subtype)
  ext l
  rw [mem_flagStabilizer, mem_flagStabilizer]
  have h := htransport (linearModel mark.model l)
  change (∀ W ∈ F.spaces, linearModel model
    ((linearModel mark.model).symm (linearModel mark.model l)) ∈ BinaryLinear.parabolic W) ↔
      (∀ W ∈ mark.flag.spaces, linearModel mark.model l ∈ BinaryLinear.parabolic W) at h
  rw [MulEquiv.symm_apply_apply] at h
  exact h.symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
end

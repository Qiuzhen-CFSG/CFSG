module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearCubic
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# TI and Borel action identify the original linear-two Sylow image

A nontrivial root subgroup normalized by the full rank-one Borel is the
entire root group; Sylow conjugacy transports the matrix proof. In the
original two-conjugate group, the nonzero central intersection and TI
hypothesis give M=N_X(V). Its prescribed Borel image then normalizes V*,
forcing V* to equal the actual Sylow image.

Source: Aschbacher–Smith E.2.14(1–2), printed pp.226–227.
-/

public section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem eq_sylow_of_borel_normalized (S : Sylow 2 SL(2,F))
    (W : Subgroup SL(2,F)) (hW : W ≤ S) (hne : W ≠ ⊥)
    (hN : normalizer (S : Set SL(2,F)) ≤ normalizer (W : Set SL(2,F))) :
    W = S := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) S (upperUnipotentSylow F 2)
  let e := MulAut.conj g
  have hS : (S : Subgroup SL(2,F)).map e.toMonoidHom = upperUnipotent F := by
    exact congrArg Sylow.toSubgroup hg
  have hWU : W.map e.toMonoidHom ≤ upperUnipotent F :=
    (map_mono hW).trans_eq hS
  have hne' : W.map e.toMonoidHom ≠ ⊥ := by
    intro he
    exact hne ((map_eq_bot_iff_of_injective (f := e.toMonoidHom) W e.injective).mp he)
  have hN' : rankOneBorel F ≤ normalizer (W.map e.toMonoidHom : Set SL(2,F)) := by
    have hh := map_mono (f := e.toMonoidHom) hN
    change (normalizer ((S : Subgroup SL(2,F)) : Set SL(2,F))).map e.toMonoidHom ≤
      (normalizer (W : Set SL(2,F))).map e.toMonoidHom at hh
    rw [map_equiv_normalizer_eq (S : Subgroup SL(2,F)) e,
      map_equiv_normalizer_eq W e,hS] at hh
    exact hh
  have he := eq_upperUnipotent_of_normalized _ hWU hne' hN'
  exact Subgroup.map_injective (f := e.toMonoidHom) e.injective (he.trans hS.symm)
end Matrix.SpecialLinearGroup

namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem linear_two_star_eq_sylow_of_TI
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* SL(2,F))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hz : Z V g ≠ ⊥)
    (S : Sylow 2 SL(2,F))
    (hTS : (T : Subgroup X).map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))) = S)
    (hMS : M.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))) =
      normalizer (S : Set SL(2,F))) :
    V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))) = S := by
  let := h.elementary
  let q := ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))
  have hM : M = normalizer (V : Set X) := by
    have hh := ChapterE.ti_generated_pair_normalizer M V hTI h.normalizer_le g hz
    rw [h.generate,top_inf_eq,top_inf_eq] at hh
    exact hh
  apply Matrix.SpecialLinearGroup.eq_sylow_of_borel_normalized S (V.map q)
  · exact (map_mono h.le_sylow).trans_eq hTS
  · intro he
    have hVJ : V ≤ J M := by
      have hh := (Subgroup.map_eq_bot_iff (f := q) V).mp he
      intro v hv
      apply (QuotientGroup.eq_one_iff v).mp
      exact ξ.map_eq_one_iff.mp (hh hv)
    exact h.V_not_le_twoCore hproper
      (hVJ.trans_eq (h.J_eq_twoCore_of_linear_two m hm hcard ξ))
  · rw [← hMS]
    exact (map_mono (f := q) hM.le).trans (V.le_normalizer_map q)
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

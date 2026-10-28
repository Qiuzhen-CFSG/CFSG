module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof

/-!
# A flag fixing a prescribed vector in the marked binary natural module

The seven powers of one explicit matrix cover the nonzero vectors. Conjugating
its point stabilizer fixes the selected vector. Applying automorphism coverage
to the inverse marking returns an actual incident flag and its point or line
side. This also gives a nonzero fixed vector when the prescribed vector is zero.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), printed p.883.
-/

public section
open Subgroup Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Selection
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open ModelProof Matrix.PSL3Two

private def cycle : SL := ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], by decide⟩

private theorem vector_orbit : ∀ v : Fin 3 → ZMod 2, v ≠ 0 →
    ∃ n : Fin 7, (cycle ^ n.val).val.mulVec ![1, 0, 0] = v := by
  decide +kernel

private theorem fixes_conjugate_point (k : SL) (a : SL)
    (ha : a ∈ modelParabolic k false) :
    a.val.mulVec (k.val.mulVec ![1, 0, 0]) = k.val.mulVec ![1, 0, 0] := by
  obtain ⟨b, hb, rfl⟩ := ha
  have h := line_fixed_by_point
    (show Multiplicative.ofAdd ![1, 0, 0] ∈ pointLine from ⟨rfl, rfl⟩) b hb
  change (k * b * k⁻¹).val.mulVec (k.val.mulVec ![1, 0, 0]) = _
  change b.val.mulVec ![1, 0, 0] = ![1, 0, 0] at h
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul]
  simp only [inv_mul_cancel_right]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h]

/-- A single actual flag fixes both the prescribed vector and a nonzero vector
under the same marking. No weak BN-pair or fixed-space premise is assumed. -/
theorem exists_fixed_flag (σ : MulAut SL) (v : Fin 3 → ZMod 2) :
    ∃ (flag : SL) (side : Bool) (w : Fin 3 → ZMod 2),
      w ≠ 0 ∧
      (∀ a ∈ modelParabolic flag side, (σ a).val.mulVec v = v) ∧
      (∀ a ∈ modelParabolic flag side, (σ a).val.mulVec w = w) := by
  have aux (w : Fin 3 → ZMod 2) (hw : w ≠ 0) :
      ∃ (flag : SL) (side : Bool),
        ∀ a ∈ modelParabolic flag side, (σ a).val.mulVec w = w := by
    obtain ⟨n, hn⟩ := vector_orbit w hw
    let k := cycle ^ n.val
    have hk (a : SL) (ha : a ∈ modelParabolic k false) : a.val.mulVec w = w := by
      rw [← hn]
      exact fixes_conjugate_point k a ha
    obtain ⟨g, ⟨hp, _⟩ | ⟨hp, _⟩⟩ := marked_pair σ.symm k false
    · refine ⟨g, false, ?_⟩
      intro a ha
      have ha' : a ∈ (modelParabolic k false).map σ.symm.toMonoidHom := by
        rw [show (modelParabolic k false).map σ.symm.toMonoidHom =
          modelParabolic g false from hp]
        exact ha
      obtain ⟨b, hb, rfl⟩ := ha'
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hk b hb
    · refine ⟨g, true, ?_⟩
      intro a ha
      have ha' : a ∈ (modelParabolic k false).map σ.symm.toMonoidHom := by
        rw [show (modelParabolic k false).map σ.symm.toMonoidHom =
          modelParabolic g true from hp]
        exact ha
      obtain ⟨b, hb, rfl⟩ := ha'
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hk b hb
  by_cases hv : v = 0
  · obtain ⟨g, i, h⟩ := aux ![1, 0, 0] (by decide)
    exact ⟨g, i, ![1, 0, 0], by decide, by simp [hv], h⟩
  · obtain ⟨g, i, h⟩ := aux v hv
    exact ⟨g, i, v, hv, h, h⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Selection

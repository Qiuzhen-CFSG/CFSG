module
public import Theory.Representation.SL3.AdjointCubicCentralizer.BinarySimple

/-!
# The binary adjoint commutant

The common fixed space of the two upper elementary matrices is the highest-root
line. A binary endomorphism commuting with PSL₃ sends a nonzero highest-root
vector to an F-scalar multiple of itself. Binary irreducibility then kills
the difference from that scalar, including for singular endomorphisms.

Source motivation: Aschbacher–Smith B.4.14, printed p.98, and the nonblock
argument for original 4.3.2, pp.618–619. These are representation consequences
of explicit action hypotheses; constructing the source Frattini marking and
discharging its action-kernel descent are separate source obligations.
-/

open Matrix Representation
open scoped MatrixGroups
namespace Representation.SL3.AdjointCubicCentralizer.GraphExtension
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (F : Type*) [Field F] [CharP F 2]
attribute [local instance] ZMod.algebra

def highestRoot : TraceZero F :=
  ⟨!![0,0,1;0,0,0;0,0,0], by simp [Matrix.trace, Fin.sum_univ_three]⟩

omit [CharP F 2] in
theorem highestRoot_ne_zero : highestRoot F ≠ 0 := by
  intro h
  have := congrArg (fun X : TraceZero F => X.val 0 2) h
  exact one_ne_zero this

private def u01 : SL(3,F) :=
  ⟨!![1,1,0;0,1,0;0,0,1], by simp [Matrix.det_fin_three]⟩
private def u12 : SL(3,F) :=
  ⟨!![1,0,0;0,1,1;0,0,1], by simp [Matrix.det_fin_three]⟩

omit [CharP F 2] in
private theorem fixed_iff_commute (g : SL(3,F)) (X : TraceZero F) :
    adjointAction F (SpecialLinearGroup.toGL g) X = X ↔ g.val * X.val = X.val * g.val := by
  constructor
  · intro h
    have he := congrArg (fun Y : TraceZero F => Y.val * g.val) h
    change (g.val * X.val * g⁻¹.val) * g.val = X.val * g.val at he
    have hi : g⁻¹.val * g.val = 1 := (SpecialLinearGroup.toGL g).inv_val
    simpa only [mul_assoc, hi, mul_one] using he
  · intro h
    apply Subtype.ext
    change g.val * X.val * g⁻¹.val = X.val
    have hi : g.val * g⁻¹.val = 1 := (SpecialLinearGroup.toGL g).val_inv
    rw [h, mul_assoc, hi, mul_one]

omit [CharP F 2] in
private theorem highestRoot_fixed (g : SL(3,F))
    (hg : g = u01 F ∨ g = u12 F) :
    adjointAction F (SpecialLinearGroup.toGL g) (highestRoot F) = highestRoot F := by
  rw [fixed_iff_commute]
  rcases hg with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [u01,u12,highestRoot,Matrix.mul_apply,Fin.sum_univ_three]

private theorem fixed_line (X : TraceZero F)
    (h01 : adjointAction F (SpecialLinearGroup.toGL (u01 F)) X = X)
    (h12 : adjointAction F (SpecialLinearGroup.toGL (u12 F)) X = X) :
    X = (X.val 0 2) • highestRoot F := by
  rw [fixed_iff_commute] at h01 h12
  have h10 := congrArg (fun Y : Mat3 F => Y 0 0) h01
  have hdiag01 := congrArg (fun Y : Mat3 F => Y 0 1) h01
  have h12z := congrArg (fun Y : Mat3 F => Y 0 2) h01
  have h20 := congrArg (fun Y : Mat3 F => Y 2 1) h01
  have h21 := congrArg (fun Y : Mat3 F => Y 1 1) h12
  have hdiag12 := congrArg (fun Y : Mat3 F => Y 1 2) h12
  have h01z := congrArg (fun Y : Mat3 F => Y 0 2) h12
  simp [u01,u12,Matrix.mul_apply,Fin.sum_univ_three] at h10 hdiag01 h12z h20 h21 hdiag12 h01z
  have ht := X.property
  change Matrix.trace X.val = 0 at ht
  simp only [Matrix.trace,Fin.sum_univ_three,Matrix.diag_apply] at ht
  have hd0 : X.val 0 0 = 0 := by
    have hd1 : X.val 1 1 = X.val 0 0 := add_left_cancel (hdiag01.trans (add_comm _ _))
    have hd2 : X.val 2 2 = X.val 1 1 := add_left_cancel (hdiag12.trans (add_comm _ _))
    rw [hd2,hd1,CharTwo.add_self_eq_zero,zero_add] at ht
    exact ht
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [highestRoot]

theorem commutant_scalar [Finite F] (hF : Nat.card F = 4)
    (f : Module.End (ZMod 2) (TraceZero F))
    (hf : ∀ (g : PSL(3,F)) v,
      f (projectiveSpecialAdjoint F g v) = projectiveSpecialAdjoint F g (f v)) :
    ∃ c : F, ∀ v, f v = c • v := by
  let ρ := restrictScalars (k := ZMod 2) (projectiveSpecialAdjoint F)
  let := projectiveSpecialAdjoint_binary_irreducible F hF
  have hh (g : SL(3,F)) (hg : g = u01 F ∨ g = u12 F) :
      adjointAction F (SpecialLinearGroup.toGL g) (f (highestRoot F)) = f (highestRoot F) := by
    have he := hf (QuotientGroup.mk g) (highestRoot F)
    change f (adjointAction F (SpecialLinearGroup.toGL g) _) =
      adjointAction F (SpecialLinearGroup.toGL g) _ at he
    rw [highestRoot_fixed F g hg] at he
    exact he.symm
  let c := (f (highestRoot F)).val 0 2
  have hc := fixed_line F (f (highestRoot F)) (hh _ (Or.inl rfl)) (hh _ (Or.inr rfl))
  let z : IntertwiningMap ρ ρ :=
    { toLinearMap := f - (c • (LinearMap.id : Module.End F (TraceZero F))).restrictScalars (ZMod 2)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        change f (projectiveSpecialAdjoint F g v) - c • projectiveSpecialAdjoint F g v =
          projectiveSpecialAdjoint F g (f v - c • v)
        rw [hf,map_sub,map_smul] }
  have hz : z (highestRoot F) = 0 := sub_eq_zero.mpr hc
  rcases IsIrreducible.injective_or_eq_zero z with hi | he
  · exact False.elim (highestRoot_ne_zero F (hi (hz.trans (map_zero z).symm)))
  · refine ⟨c,fun v => sub_eq_zero.mp ?_⟩
    exact congrArg (fun w : IntertwiningMap ρ ρ => w v) he

end
end Representation.SL3.AdjointCubicCentralizer.GraphExtension

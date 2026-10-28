module
public import Theory.Representation.SL3.AdjointCubicCentralizer.Projective
/-!
# Faithfulness of the determinant-twisted projective adjoint action

A kernel element fixes a nonzero trace-zero idempotent. Idempotency forces
its determinant to be one. Its ordinary conjugation action then fixes all
trace-zero matrices; decomposing an arbitrary matrix into its trace-zero
part and a scalar proves that the element is central in GL₃. Hence it is
trivial in the actual projective quotient.

This checks the faithfulness hypothesis for the alternative extension in
Aschbacher--Smith B.4.14, printed p.98. Binary irreducibility and the source
parabolic chief-factor profile are separate obligations.
-/

open Matrix
namespace Representation.SL3.AdjointCubicCentralizer
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (F : Type*) [Field F] [CharP F 2]

private theorem trace_one_three : Matrix.trace (1 : Mat3 F) = 1 := by
  rw [Matrix.trace_one]
  rw [Fintype.card_fin]
  calc
    (3 : F) = (1+1)+1 := by ring
    _ = 1 := by rw [CharTwo.add_self_eq_zero,zero_add]

private theorem twisted_kernel_det (g : (Mat3 F)ˣ)
    (h : twistedAdjointAction F g = 1) : Matrix.det g.val = 1 := by
  let X : Mat3 F := block F 0 1
  have ht : Matrix.trace X = 0 := by
    simp [X,block,Matrix.trace,Fin.sum_univ_three,CharTwo.add_self_eq_zero]
  have hi : X*X=X := by simp [X,block_mul]
  have hx : Matrix.det g.val • (g.val*X*g⁻¹.val) = X :=
    congrArg Subtype.val (LinearMap.congr_fun h ⟨X,ht⟩)
  have hs : (g.val*X*g⁻¹.val)*(g.val*X*g⁻¹.val) = g.val*X*g⁻¹.val := by
    calc
      _ = g.val * (X*X) * g⁻¹.val := by
        calc
          _ = (g.val*X)*(g⁻¹.val*g.val)*X*g⁻¹.val := by simp only [mul_assoc]
          _ = _ := by simp only [Units.inv_mul,mul_one,mul_assoc]
      _ = _ := by rw [hi]
  have hh : Matrix.det g.val • X = X := by
    calc
      _ = Matrix.det g.val • (Matrix.det g.val • (g.val*X*g⁻¹.val)) := by rw [hx]
      _ = (Matrix.det g.val • (g.val*X*g⁻¹.val)) *
            (Matrix.det g.val • (g.val*X*g⁻¹.val)) := by rw [smul_mul_smul,hs,smul_smul]
      _ = X := by rw [hx,hi]
  simpa [X,block] using congrArg (fun A : Mat3 F => A 1 1) hh

private theorem adjoint_kernel_central (g : (Mat3 F)ˣ)
    (h : adjointAction F g = 1) : g ∈ Subgroup.center (Mat3 F)ˣ := by
  apply Subgroup.mem_center_iff.mpr
  intro a
  let X : Mat3 F := a.val - Matrix.trace a.val • 1
  have ht : Matrix.trace X = 0 := by
    rw [Matrix.trace_sub,Matrix.trace_smul,trace_one_three,smul_eq_mul,mul_one,sub_self]
  have hx : g.val*X*g⁻¹.val=X :=
    congrArg Subtype.val (LinearMap.congr_fun h ⟨X,ht⟩)
  have he : g.val*a.val*g⁻¹.val=a.val := by
    have hz : g.val*(Matrix.trace a.val • (1 : Mat3 F))*g⁻¹.val = Matrix.trace a.val • 1 := by
      simp
    change g.val*(a.val-Matrix.trace a.val • 1)*g⁻¹.val = a.val-Matrix.trace a.val • 1 at hx
    rw [mul_sub,sub_mul,hz] at hx
    exact sub_left_inj.mp hx
  apply Units.ext
  change a.val*g.val=g.val*a.val
  have he' := congrArg (fun M : Mat3 F => M*g.val) he
  simpa only [mul_assoc,Units.inv_mul,mul_one] using he'.symm

/-- The determinant-twisted action of the actual projective group is faithful. -/
theorem projectiveTwistedAdjoint_injective (hc : ∀ u : Fˣ, u^3=1) :
    Function.Injective (projectiveTwistedAdjoint F hc) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Mat3 F)ˣ) x
  have hh : twistedAdjointAction F g = 1 := hx
  have hd := twisted_kernel_det F g hh
  have ha : adjointAction F g = 1 := by
    apply LinearMap.ext
    intro X
    have he := LinearMap.congr_fun hh X
    apply Subtype.ext
    have he' := congrArg Subtype.val he
    change Matrix.det g.val • (g.val*X.val*g⁻¹.val)=X.val at he'
    change g.val*X.val*g⁻¹.val=X.val
    simpa only [hd,one_smul] using he'
  exact (QuotientGroup.eq_one_iff _).mpr (adjoint_kernel_central F g ha)
end
end Representation.SL3.AdjointCubicCentralizer

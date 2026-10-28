import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Constructions
set_option warningAsError false

/-! Hyperbolic splitting for alternating forms over arbitrary fields. -/
noncomputable section
namespace Atlas.AlternatingForm
open LinearMap
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) (hA : B.IsAlt)

/-- Nondegeneracy supplies a normalized partner without a characteristic restriction. -/
theorem exists_partner (hB : B.Nondegenerate) {e : V} (he : e ≠ 0) :
    ∃ f, B e f = 1 := by
  obtain ⟨v,hv⟩ : ∃ v, B e v ≠ 0 := by
    by_contra! h
    exact he (hB.1 e h)
  exact ⟨(B e v)⁻¹ • v, by simp [map_smul, hv]⟩

variable (e f : V) (hef : B e f = 1)

/-- The simultaneous orthogonal complement of the selected hyperbolic pair. -/
def complement : Submodule F V := (B.flip e).ker ⊓ (B.flip f).ker

@[simp] theorem mem_complement (x : V) :
    x ∈ complement B e f ↔ B x e = 0 ∧ B x f = 0 := Iff.rfl

/-- Projection onto the selected plane, in its normalized coordinates. -/
def planeProjection : V →ₗ[F] V := (B.flip f).smulRight e - (B.flip e).smulRight f

@[simp] theorem planeProjection_apply (x : V) :
    planeProjection B e f x = (B x f) • e - (B x e) • f := rfl

include hA hef
theorem reversed_pairing : B f e = -1 := by rw [← hA.neg_eq e f, hef]

@[simp] theorem projection_e : planeProjection B e f e = e := by
  simp [planeProjection_apply, hef, hA.self_eq_zero]

@[simp] theorem projection_f : planeProjection B e f f = f := by
  simp [planeProjection_apply, reversed_pairing B hA e f hef, hA.self_eq_zero]

theorem remainder_mem (x : V) : x - planeProjection B e f x ∈ complement B e f := by
  simp only [mem_complement, planeProjection_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hA.self_eq_zero,
    reversed_pairing B hA e f hef, hef]
  constructor <;> ring

/-- The hyperbolic coordinates plus the actual complement give a direct decomposition. -/
def split : V ≃ₗ[F] (F × F) × complement B e f where
  toFun x := ((B x f, -B x e), ⟨x-planeProjection B e f x, remainder_mem B hA e f hef x⟩)
  invFun z := z.1.1 • e + z.1.2 • f + z.2.val
  left_inv x := by
    simp only [planeProjection_apply, neg_smul]
    abel
  right_inv z := by
    rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
    have hw' := (mem_complement B e f w).mp hw
    apply Prod.ext
    · apply Prod.ext <;>
        simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          hef, hA.self_eq_zero, reversed_pairing B hA e f hef, hw'.1, hw'.2]
    · apply Subtype.ext
      simp only [planeProjection_apply, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, hef, hA.self_eq_zero,
        reversed_pairing B hA e f hef, hw'.1, hw'.2]
      simp
  map_add' x y := by
    apply Prod.ext
    · simp [map_add, neg_add, add_comm]
    · apply Subtype.ext
      change x+y-planeProjection B e f (x+y) =
        (x-planeProjection B e f x)+(y-planeProjection B e f y)
      rw [map_add]
      abel
  map_smul' r x := by
    apply Prod.ext
    · simp [map_smul, mul_neg]
    · apply Subtype.ext
      simp [map_smul, smul_sub]

/-- The alternating restriction on the actual complement. -/
theorem complement_alternating : (B.restrict (complement B e f)).IsAlt := by
  intro x
  exact hA.self_eq_zero x.val

/-- Nondegeneracy survives hyperbolic splitting. -/
theorem complement_nondegenerate (hB : B.Nondegenerate) :
    (B.restrict (complement B e f)).Nondegenerate := by
  have hs : (B.restrict (complement B e f)).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hB.1 x.val
    intro y
    obtain ⟨z,rfl⟩ := (split B hA e f hef).symm.surjective y
    rcases z with ⟨⟨r,s⟩,w⟩
    have hp := x.prop
    have hz : B x.val w.val = 0 := hx w
    change B x.val (r • e + s • f + w.val) = 0
    simp [map_add, map_smul, (mem_complement B e f x.val).mp hp, hz]
  refine ⟨hs, ?_⟩
  intro x hx
  apply hs x
  intro y
  change B x.val y.val = 0
  rw [← hA.neg_eq y.val x.val]
  change -((B.restrict (complement B e f)) y x) = 0
  rw [hx y, neg_zero]

theorem finrank_complement [FiniteDimensional F V] :
    Module.finrank F (complement B e f) + 2 = Module.finrank F V := by
  have h := (split B hA e f hef).finrank_eq
  simpa [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using h.symm


/-- The decomposition is orthogonal and has the normalized hyperbolic plane form. -/
theorem split_form (z z' : (F × F) × complement B e f) :
    B ((split B hA e f hef).symm z) ((split B hA e f hef).symm z') =
      z.1.1*z'.1.2-z.1.2*z'.1.1+B z.2.val z'.2.val := by
  rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
  rcases z' with ⟨⟨t,u⟩,⟨v,hv⟩⟩
  have hw := (mem_complement B e f w).mp hw
  have hv := (mem_complement B e f v).mp hv
  have hev : B e v = 0 := by rw [← hA.neg_eq v e, hv.1, neg_zero]
  have hfv : B f v = 0 := by rw [← hA.neg_eq v f, hv.2, neg_zero]
  change B (r • e+s • f+w) (t • e+u • f+v) = r*u-s*t+B w v
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hA.self_eq_zero, hef, reversed_pairing B hA e f hef,
    hw.1, hw.2, hev, hfv]
  ring

end Atlas.AlternatingForm


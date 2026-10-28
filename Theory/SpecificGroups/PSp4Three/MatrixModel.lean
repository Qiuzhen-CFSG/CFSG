module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

/-!
# The symplectic matrix carrier and alternating frames

Characteristic-independent matrix and alternating-form proofs supporting the
concrete ternary simplicity theorem. This local module port is required because
the older shared symplectic ports are not Lean modules.

Adapted from Gerald Höhn, ATLAS, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
from `Atlas/LinearGroups/Symplectic/Basic.lean`, `Atlas/LinearAlgebra/SymplecticBasis.lean`, `Atlas/LinearGroups/Symplectic/Basis.lean`.
Covered adaptations retain the ATLAS Research and Attribution License 1.0
(`LICENSES/ATLAS.txt`; citation: `LICENSES/ATLAS-CITATION.cff`).
Changes: CFSG imports and module boundaries; local namespace to avoid
collisions with other ports; unused results outside this argument omitted.
-/

@[expose] public section

/-! The primary matrix model and its alternating form, in every characteristic. -/
noncomputable section
namespace Matrix.PSp4Three
open Matrix

abbrev Index (n : ℕ) := Fin n ⊕ Fin n
abbrev Vector (n : ℕ) (F : Type*) := Index n → F
abbrev Sp (n : ℕ) (F : Type*) [CommRing F] := ↥(Matrix.symplecticGroup (Fin n) F)
abbrev PSp (n : ℕ) (F : Type*) [CommRing F] := Sp n F ⧸ Subgroup.center (Sp n F)

variable {n : ℕ} {F : Type*} [CommRing F]

instance finite_sp [Finite F] : Finite (Sp n F) := inferInstance
instance finite_psp [Finite F] : Finite (PSp n F) := inferInstance

def projection : Sp n F →* PSp n F := QuotientGroup.mk' _

theorem projection_surjective : Function.Surjective (projection (n := n) (F := F)) :=
  QuotientGroup.mk'_surjective _

theorem projection_kernel : (projection (n := n) (F := F)).ker = Subgroup.center (Sp n F) :=
  QuotientGroup.ker_mk' _

/-- The form with positive pairing from the first half to the second half. -/
def form : LinearMap.BilinForm F (Vector n F) := (-Matrix.J (Fin n) F).toBilin'

theorem form_apply (x y : Vector n F) :
    form x y = ∑ i : Fin n, (x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i)) := by
  simp [form, Matrix.toBilin'_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply,
    Fintype.sum_sum_type, sub_eq_add_neg, Finset.sum_add_distrib]

@[simp] theorem form_self (x : Vector n F) : form x x = 0 := by
  simp [form_apply, mul_comm]

theorem form_alternating : (form (n := n) (F := F)).IsAlt := form_self

theorem form_swap (x y : Vector n F) : form x y = -form y x := by
  simp only [form_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

def e (i : Fin n) : Vector n F := Pi.single (.inl i) 1
def f (i : Fin n) : Vector n F := Pi.single (.inr i) 1

@[simp] theorem form_e_right (x : Vector n F) (i : Fin n) : form x (e i) = -x (.inr i) := by
  simp [form_apply, e, Pi.single_apply]

@[simp] theorem form_f_right (x : Vector n F) (i : Fin n) : form x (f i) = x (.inl i) := by
  simp [form_apply, f, Pi.single_apply]

theorem form_left_separating (x : Vector n F) (hx : ∀ y, form x y = 0) : x = 0 := by
  funext i
  cases i with
  | inl i => simpa only [form_f_right, Pi.zero_apply] using hx (f i)
  | inr i => simpa only [form_e_right, neg_eq_zero, Pi.zero_apply] using hx (e i)

theorem form_nondegenerate : (form (n := n) (F := F)).Nondegenerate := by
  constructor
  · exact form_left_separating
  · intro y hy
    apply form_left_separating y
    intro x
    rw [form_swap, hy x, neg_zero]

/-- The column convention preserves the same carrier, also in characteristic two. -/
theorem mem_iff_preserves {A : Matrix (Index n) (Index n) F} :
    A ∈ Matrix.symplecticGroup (Fin n) F ↔ ∀ x y, form (A *ᵥ x) (A *ᵥ y) = form x y := by
  rw [SymplecticGroup.mem_iff']
  have he : ∀ A : Matrix (Index n) (Index n) F,
      (form (n := n) (F := F)).comp A.toLin' A.toLin' = (Aᵀ * (-J (Fin n) F) * A).toBilin' :=
    fun A => Matrix.toBilin'_comp _ _ _
  constructor
  · intro h x y
    have h' : Aᵀ * (-J (Fin n) F) * A = -J (Fin n) F := by simp [h]
    have hform := he A
    rw [h'] at hform
    exact congrArg (fun B : LinearMap.BilinForm F (Vector n F) => B x y) hform
  · intro h
    have hform : (form (n := n) (F := F)).comp A.toLin' A.toLin' = form := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact h x y
    rw [he A] at hform
    have hm := Matrix.toBilin'.injective hform
    simpa [Matrix.mul_neg, Matrix.neg_mul] using hm

theorem preserves (g : Sp n F) (x y : Vector n F) :
    form ((g.val) *ᵥ x) ((g.val) *ᵥ y) = form x y := mem_iff_preserves.mp g.prop x y

theorem smul_eq_mulVec (g : Sp n F) (x : Vector n F) :
    g • x = g.val *ᵥ x := rfl

instance faithful_linear_action : FaithfulSMul (Sp n F) (Vector n F) where
  eq_of_smul_eq_smul h := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have hv := congrFun (h (Pi.single j 1)) i
    simpa [smul_eq_mulVec, Matrix.mulVec_single] using hv

def toGL : Sp n F →* Matrix.GeneralLinearGroup (Index n) F where
  toFun g := Matrix.GeneralLinearGroup.mk'' g.val (SymplecticGroup.symplectic_det g.prop)
  map_one' := by apply Units.ext; rfl
  map_mul' _ _ := by apply Units.ext; rfl

theorem toGL_injective : Function.Injective (toGL (n := n) (F := F)) := by
  intro x y h
  exact Subtype.ext (congrArg Units.val h)

theorem determinant_one (g : Sp n F) : Matrix.det g.val = 1 :=
  SymplecticGroup.det_eq_one g.prop

end Matrix.PSp4Three
end

/-! Hyperbolic splitting for alternating forms over arbitrary fields. -/
noncomputable section
namespace Matrix.PSp4Three.Frame
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
      simp only [planeProjection_apply, map_add, map_smul, hef, hA.self_eq_zero,
        reversed_pairing B hA e f hef, hw'.1, hw'.2]
      simp
  map_add' x y := by
    apply Prod.ext
    · simp [map_add, add_comm]
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

omit hef in
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

end Matrix.PSp4Three.Frame
end

noncomputable section
namespace Matrix.PSp4Three
variable {F : Type*} [Field F]

/-- Split the first coordinate of each half, retaining the fixed index marking. -/
def headTail (n : ℕ) : Vector (n+1) F ≃ₗ[F] (F × F) × Vector n F where
  toFun x := ((x (.inl 0),x (.inr 0)),Sum.elim (fun i => x (.inl i.succ))
    (fun i => x (.inr i.succ)))
  invFun z := Sum.elim (Fin.cases z.1.1 (fun i => z.2 (.inl i)))
    (Fin.cases z.1.2 (fun i => z.2 (.inr i)))
  left_inv x := by
    funext i
    rcases i with i|i <;> refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · funext i
      cases i <;> rfl
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext i
      cases i <;> rfl
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · funext i
      cases i <;> rfl

theorem form_headTail {n : ℕ} (x y : Vector (n+1) F) :
    form x y = (headTail n x).1.1*(headTail n y).1.2 -
      (headTail n x).1.2*(headTail n y).1.1 + form (headTail n x).2 (headTail n y).2 := by
  simp only [form_apply, Fin.sum_univ_succ]
  rfl


/-- Every finite-dimensional nondegenerate alternating form of dimension 2n
is isometric to the retained standard matrix form. -/
theorem exists_isometry {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (n : ℕ) (B : LinearMap.BilinForm F V)
    (hA : B.IsAlt) (hB : B.Nondegenerate) (hdim : Module.finrank F V = 2*n) :
    Nonempty (B.IsometryEquiv (form (n := n) (F := F))) := by
  induction n generalizing V with
  | zero =>
    let : Subsingleton V := Module.finrank_zero_iff.mp (by simpa using hdim)
    refine ⟨{ toLinearEquiv := LinearEquiv.ofSubsingleton (R := F) V (Vector 0 F)
              map_app' := ?_ }⟩
    intro x y
    rw [Subsingleton.elim x 0, Subsingleton.elim y 0]
    simp
  | succ n ih =>
    let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank F V)
    obtain ⟨e,he⟩ := exists_ne (0 : V)
    obtain ⟨f,hef⟩ := Matrix.PSp4Three.Frame.exists_partner B hB he
    let W := Matrix.PSp4Three.Frame.complement B e f
    let C := B.restrict W
    have hC : C.IsAlt := Matrix.PSp4Three.Frame.complement_alternating B hA e f
    have hCN : C.Nondegenerate :=
      Matrix.PSp4Three.Frame.complement_nondegenerate B hA e f hef hB
    have hW : Module.finrank F W = 2*n := by
      have h := Matrix.PSp4Three.Frame.finrank_complement B hA e f hef
      change Module.finrank F W + 2 = Module.finrank F V at h
      omega
    obtain ⟨k⟩ := ih C hC hCN hW
    let s := Matrix.PSp4Three.Frame.split B hA e f hef
    let t : V ≃ₗ[F] Vector (n+1) F :=
      (s.trans ((LinearEquiv.refl F (F × F)).prodCongr k.toLinearEquiv)).trans
        (headTail n).symm
    refine ⟨{ toLinearEquiv := t, map_app' := ?_ }⟩
    intro x y
    change form (t x) (t y) = B x y
    rw [form_headTail]
    have ht (z : V) : headTail n (t z) = ((s z).1,k (s z).2) := by
      simp [t]
    rw [ht, ht]
    have hk := k.map_app (s y).2 (s x).2
    change form (k (s x).2) (k (s y).2) = B (s x).2.val (s y).2.val at hk
    rw [hk]
    have hb := Matrix.PSp4Three.Frame.split_form B hA e f hef (s x) (s y)
    simpa only [s, LinearEquiv.symm_apply_apply] using hb.symm


/-- A prescribed hyperbolic pair can be the first pair of standard coordinates. -/
theorem exists_isometry_pair {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (n : ℕ) (B : LinearMap.BilinForm F V)
    (hA : B.IsAlt) (hB : B.Nondegenerate) (hdim : Module.finrank F V = 2*(n+1))
    (u v : V) (huv : B u v = 1) :
    ∃ g : B.IsometryEquiv (form (n := n+1) (F := F)),
      g u = e 0 ∧ g v = f 0 := by
  let W := Matrix.PSp4Three.Frame.complement B u v
  let C := B.restrict W
  have hC := Matrix.PSp4Three.Frame.complement_alternating B hA u v
  have hCN := Matrix.PSp4Three.Frame.complement_nondegenerate B hA u v huv hB
  have hW : Module.finrank F W = 2*n := by
    have h := Matrix.PSp4Three.Frame.finrank_complement B hA u v huv
    change Module.finrank F W + 2 = Module.finrank F V at h
    omega
  obtain ⟨k⟩ := exists_isometry n C hC hCN hW
  let s := Matrix.PSp4Three.Frame.split B hA u v huv
  let t : V ≃ₗ[F] Vector (n+1) F :=
    (s.trans ((LinearEquiv.refl F (F × F)).prodCongr k.toLinearEquiv)).trans
      (headTail n).symm
  have ht (z : V) : headTail n (t z) = ((s z).1,k (s z).2) := by simp [t]
  have htB : ∀ x y, form (t x) (t y) = B x y := by
    intro x y
    rw [form_headTail, ht, ht]
    have hk := k.map_app (s y).2 (s x).2
    change form (k (s x).2) (k (s y).2) = B (s x).2.val (s y).2.val at hk
    rw [hk]
    have hb := Matrix.PSp4Three.Frame.split_form B hA u v huv (s x) (s y)
    simpa only [s, LinearEquiv.symm_apply_apply] using hb.symm
  refine ⟨{ toLinearEquiv := t, map_app' := htB }, ?_, ?_⟩
  · change t u = e 0
    apply (headTail n).injective
    rw [ht]
    have hs : s u = ((1,0),0) := by
      apply Prod.ext
      · simp [s, Matrix.PSp4Three.Frame.split, huv, hA.self_eq_zero]
      · apply Subtype.ext
        change u-Matrix.PSp4Three.Frame.planeProjection B u v u=0
        rw [Matrix.PSp4Three.Frame.projection_e B hA u v huv, sub_self]
    rw [hs]
    simp [headTail, e]
    rfl
  · change t v = f 0
    apply (headTail n).injective
    rw [ht]
    have hs : s v = ((0,1),0) := by
      apply Prod.ext
      · simp [s, Matrix.PSp4Three.Frame.split, hA.self_eq_zero,
          Matrix.PSp4Three.Frame.reversed_pairing B hA u v huv]
      · apply Subtype.ext
        change v-Matrix.PSp4Three.Frame.planeProjection B u v v=0
        rw [Matrix.PSp4Three.Frame.projection_f B hA u v huv, sub_self]
    rw [hs]
    simp [headTail, f]
    rfl

end Matrix.PSp4Three
end

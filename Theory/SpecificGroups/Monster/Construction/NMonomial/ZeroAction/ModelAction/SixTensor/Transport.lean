module
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.ModelAction.SixTensor.Geometry
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Functorial geometric transport of the six tensor factors

An ambient Parker permutation which carries both halfspace families and
intertwines the literal pairing and sign involutions induces a linear
isometry between the corresponding tensor factors. Restriction to the actual
axes supplies the spin transport; halfspace images supply the natural
transport. The signed formulas prove composition, identity and monomiality.
`AxisTransportData` gives such a transport for every element of N and the
actual diagonal action on ordered pairs, without assuming any representation.

Source: Aschbacher, *Sporadic Groups*, Sections 14 and 27, and 29.7.5 on
printed p. 156. Products use left function composition.
-/

@[expose] public section
noncomputable section
open Atlas.Fischer Atlas.Codes
open Sporadic.Monster.Construction.TrialitySpin
open SignedModules SpinActions
open scoped TensorProduct
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction.SixTensor

/-- A geometric transport, before passing to orbit modules or tensor products. -/
structure GeometricTransport (p q : Slot) where
  ambient : Equiv.Perm Triple
  natural_halfspaces : Natural.Carries p.natural q.natural ambient
  spin_halfspaces : Natural.Carries p.spin q.spin ambient
  pairing : ∀ a, ambient ((axisK p.natural).val a) = (axisK q.natural).val (ambient a)
  signs : ∀ a, ambient ((axisZ p.natural).val a) = (axisZ q.natural).val (ambient a)

namespace GeometricTransport
variable {p q r : Slot}

@[ext] theorem ext (t u : GeometricTransport p q) (h : t.ambient = u.ambient) : t = u := by
  cases t; cases u; cases h; rfl

/-- Restriction of the literal permutation to the literal Parker axes. -/
def point (t : GeometricTransport p q) : Points p.spin ≃ Points q.spin :=
  (t.ambient.image (Set.range (Natural.point p.spin))).trans
    (Equiv.setCongr (Natural.image_axis t.ambient t.spin_halfspaces))

@[simp] theorem point_val (t : GeometricTransport p q) (a : Points p.spin) :
    (t.point a).val = t.ambient a.val := rfl

theorem point_pair (t : GeometricTransport p q) (a : Points p.spin) :
    t.point ((geometry p).pairing.flip a) = (geometry q).pairing.flip (t.point a) := by
  apply Subtype.ext
  simp only [point_val, pairing_val, t.pairing]

theorem point_sign (t : GeometricTransport p q) (a : Points p.spin) :
    t.point ((geometry p).signs.flip a) = (geometry q).signs.flip (t.point a) := by
  apply Subtype.ext
  simp only [point_val, signs_val, t.signs]

def spin (t : GeometricTransport p q) : Spin p ≃ₗ[ℝ] Spin q :=
  (geometry p).transport (geometry q) t.point t.point_pair t.point_sign

@[simp] theorem spin_vector (t : GeometricTransport p q) (a : Points p.spin) :
    t.spin ((geometry p).vector a) = (geometry q).vector (t.point a) :=
  (geometry p).transport_vector (geometry q) _ _ _ a

def loop (t : GeometricTransport p q) : Equiv.Perm ParkerLoop :=
  (param p.spin).trans (t.point.trans (param q.spin).symm)

@[simp] theorem point_param (t : GeometricTransport p q) (b : ParkerLoop) :
    t.point (param p.spin b) = param q.spin (t.loop b) := by
  simp [loop]

/-- The loop coordinates still represent the actual ambient point map. -/
theorem loop_point (t : GeometricTransport p q) (b : ParkerLoop) :
    Natural.point q.spin (t.loop b) = t.ambient (Natural.point p.spin b) :=
  congrArg Subtype.val (t.point_param b).symm

@[simp] theorem spin_delta (t : GeometricTransport p q) (b : ParkerLoop) :
    t.spin (delta p b) = delta q (t.loop b) := by
  change t.spin ((geometry p).vector (param p.spin b)) = _
  rw [spin_vector, point_param]
  rfl

def natural (t : GeometricTransport p q) : Natural.Space p.natural ≃ₗ[ℝ] Natural.Space q.natural :=
  Natural.transport t.ambient t.natural_halfspaces

def label (t : GeometricTransport p q) : Equiv.Perm Natural.Label :=
  Natural.labelEquiv t.ambient t.natural_halfspaces

@[simp] theorem natural_L (t : GeometricTransport p q) (ε : ParkerBit) (x : Omega) :
    t.natural (Natural.L p.natural ε x) =
      Natural.L q.natural (t.label (x,ε)).2 (t.label (x,ε)).1 :=
  Natural.transport_L _ _ ε x

/-- The source tensor transport is induced by its two actual geometric actions. -/
def tensor (t : GeometricTransport p q) : Tensor p ≃ₗ[ℝ] Tensor q :=
  TensorProduct.congr t.natural t.spin

@[simp] theorem tensor_tmul (t : GeometricTransport p q) (a : Natural.Space p.natural)
    (v : Spin p) : t.tensor (a ⊗ₜ[ℝ] v) = t.natural a ⊗ₜ[ℝ] t.spin v := rfl

/-- Formula 29.7.5 before identifying the two orientations. -/
theorem tensor_signed (t : GeometricTransport p q) (ε : ParkerBit) (x : Omega) (b : ParkerLoop) :
    t.tensor (Natural.L p.natural ε x ⊗ₜ[ℝ] delta p b) =
      Natural.L q.natural (t.label (x,ε)).2 (t.label (x,ε)).1 ⊗ₜ[ℝ]
        delta q (t.loop b) := by rw [tensor_tmul, natural_L, spin_delta]

/-- A usable formula with explicitly calculated halfspace and Parker images. -/
theorem tensor_of_images (t : GeometricTransport p q) (ε η : ParkerBit)
    (x y : Omega) (b c : ParkerLoop)
    (hL : t.ambient '' Natural.halfspace p.natural (x,ε) = Natural.halfspace q.natural (y,η))
    (hb : t.ambient (Natural.point p.spin b) = Natural.point q.spin c) :
    t.tensor (Natural.L p.natural ε x ⊗ₜ[ℝ] delta p b) =
      Natural.L q.natural η y ⊗ₜ[ℝ] delta q c := by
  have hl : t.label (x,ε) = (y,η) := Natural.labelEquiv_of_image _ _ _ _ hL
  have hc : t.loop b = c := (Natural.point_injective q.spin) ((t.loop_point b).trans hb)
  rw [tensor_signed, hl, hc]

def refl (p : Slot) : GeometricTransport p p where
  ambient := Equiv.refl _
  natural_halfspaces l := ⟨l, by simp⟩
  spin_halfspaces l := ⟨l, by simp⟩
  pairing _ := rfl
  signs _ := rfl

/-- Forward composition, matching `Equiv.trans`. -/
def trans (t : GeometricTransport p q) (u : GeometricTransport q r) : GeometricTransport p r where
  ambient := t.ambient.trans u.ambient
  natural_halfspaces l := by
    obtain ⟨m,hm⟩ := t.natural_halfspaces l
    obtain ⟨n,hn⟩ := u.natural_halfspaces m
    exact ⟨n, by change (u.ambient ∘ t.ambient) '' _ = _; rw [Set.image_comp, hm, hn]⟩
  spin_halfspaces l := by
    obtain ⟨m,hm⟩ := t.spin_halfspaces l
    obtain ⟨n,hn⟩ := u.spin_halfspaces m
    exact ⟨n, by change (u.ambient ∘ t.ambient) '' _ = _; rw [Set.image_comp, hm, hn]⟩
  pairing a := by change u.ambient (t.ambient _) = _; rw [t.pairing, u.pairing]; rfl
  signs a := by change u.ambient (t.ambient _) = _; rw [t.signs, u.signs]; rfl

@[simp] theorem point_trans (t : GeometricTransport p q) (u : GeometricTransport q r)
    (a : Points p.spin) : (t.trans u).point a = u.point (t.point a) := Subtype.ext rfl

@[simp] theorem label_trans (t : GeometricTransport p q) (u : GeometricTransport q r)
    (l : Natural.Label) : (t.trans u).label l = u.label (t.label l) := by
  apply Natural.labelEquiv_of_image
  change (u.ambient ∘ t.ambient) '' _ = _
  rw [Set.image_comp, Natural.image_halfspace t.ambient t.natural_halfspaces,
    Natural.image_halfspace u.ambient u.natural_halfspaces]
  rfl

@[simp] theorem spin_trans (t : GeometricTransport p q) (u : GeometricTransport q r) :
    (t.trans u).spin = t.spin.trans u.spin := by
  apply LinearEquiv.toLinearMap_injective
  apply (geometry p).vector_ext
  intro a
  change (t.trans u).spin ((geometry p).vector a) = u.spin (t.spin ((geometry p).vector a))
  rw [spin_vector, spin_vector, spin_vector, point_trans]

@[simp] theorem natural_trans (t : GeometricTransport p q) (u : GeometricTransport q r) :
    (t.trans u).natural = t.natural.trans u.natural := by
  apply LinearEquiv.toLinearMap_injective
  apply (Natural.basis p.natural).ext
  intro x
  change (t.trans u).natural (Natural.basis p.natural x) = u.natural (t.natural (Natural.basis p.natural x))
  rw [Natural.basis_eq_L, natural_L, natural_L, natural_L]
  simp only [label_trans]

@[simp] theorem tensor_trans (t : GeometricTransport p q) (u : GeometricTransport q r) :
    (t.trans u).tensor = t.tensor.trans u.tensor := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro a v
  change (t.trans u).tensor (a ⊗ₜ[ℝ] v) = u.tensor (t.tensor (a ⊗ₜ[ℝ] v))
  rw [tensor_tmul, tensor_tmul, tensor_tmul, natural_trans, spin_trans]
  rfl

@[simp] theorem tensor_refl (p : Slot) : (refl p).tensor = LinearEquiv.refl ℝ (Tensor p) := by
  apply LinearEquiv.toLinearMap_injective
  apply marked_ext p
  intro x b
  change (refl p).tensor (Natural.L p.natural 1 x ⊗ₜ[ℝ] delta p b) = _
  exact tensor_of_images (refl p) 1 1 x x b b (by simp [refl]) rfl

theorem spin_isometry (t : GeometricTransport p q) (v w : Spin p) :
    spinForm q (t.spin v) (t.spin w) = spinForm p v w :=
  (geometry p).transport_isometry (geometry q) _ _ _ v w

/-- Transport permutes the marked signed families; no choice of orbit representatives is used. -/
theorem tensor_monomial (t : GeometricTransport p q) (x : Omega) (b : ParkerLoop) :
    ∃ y c, t.tensor (marked p x b) = marked q y c ∨
      t.tensor (marked p x b) = -marked q y c := by
  obtain ⟨y,hy⟩ := Natural.transport_monomial t.ambient t.natural_halfspaces x
  refine ⟨y,t.loop b,?_⟩
  change t.natural (Natural.L p.natural 1 x) ⊗ₜ[ℝ] t.spin (delta p b) = _ ∨
    t.natural (Natural.L p.natural 1 x) ⊗ₜ[ℝ] t.spin (delta p b) = _
  rw [spin_delta]
  simp only [Natural.basis_eq_L] at hy
  rcases hy with hy | hy
  · exact Or.inl (congrArg (fun a => a ⊗ₜ[ℝ] delta q (t.loop b)) hy)
  · right
    rw [show t.natural (Natural.L p.natural 1 x) = -Natural.L q.natural 1 y from hy,
      TensorProduct.neg_tmul]
    rfl

end GeometricTransport

/-- The source form on each natural-by-spin factor. -/
def tensorForm (p : Slot) : LinearMap.BilinForm ℝ (Tensor p) :=
  (Natural.form p.natural).tmul (spinForm p)

theorem GeometricTransport.tensor_isometry {p q : Slot} (t : GeometricTransport p q)
    (v w : Tensor p) : tensorForm q (t.tensor v) (t.tensor w) = tensorForm p v w := by
  have he : (tensorForm q).compl₁₂ t.tensor.toLinearMap t.tensor.toLinearMap = tensorForm p := by
    apply TensorProduct.ext'
    intro a s
    apply TensorProduct.ext'
    intro b u
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, GeometricTransport.tensor_tmul,
      tensorForm, LinearMap.BilinForm.tensorDistrib_tmul]
    rw [t.spin_isometry]
    change spinForm p s u • Natural.form q.natural
      (Natural.transport t.ambient t.natural_halfspaces a)
      (Natural.transport t.ambient t.natural_halfspaces b) = _
    rw [Natural.transport_isometry]
  exact LinearMap.congr_fun (LinearMap.congr_fun he v) w

/-- The actual diagonal permutation of the six ordered pairs. -/
def slotPerm (e : Equiv.Perm Natural.Axis) : Equiv.Perm Slot where
  toFun p := ⟨(e p.natural,e p.spin), fun h => p.prop (e.injective h)⟩
  invFun p := ⟨(e.symm p.natural,e.symm p.spin), fun h => p.prop (e.symm.injective h)⟩
  left_inv p := by apply Subtype.ext; exact Prod.ext (e.symm_apply_apply _) (e.symm_apply_apply _)
  right_inv p := by apply Subtype.ext; exact Prod.ext (e.apply_symm_apply _) (e.apply_symm_apply _)

@[simp] theorem slotPerm_natural (e : Equiv.Perm Natural.Axis) (p : Slot) :
    (slotPerm e p).natural = e p.natural := rfl
@[simp] theorem slotPerm_spin (e : Equiv.Perm Natural.Axis) (p : Slot) :
    (slotPerm e p).spin = e p.spin := rfl

def slotPermutation (H : AxisTransportData) : N →* Equiv.Perm Slot where
  toFun g := slotPerm (H.permutation g)
  map_one' := by
    ext p : 1
    apply Subtype.ext
    change ((H.permutation 1) p.natural, (H.permutation 1) p.spin) = p.val
    rw [map_one]
    rfl
  map_mul' g h := by
    ext p : 1
    apply Subtype.ext
    change ((H.permutation (g*h)) p.natural, (H.permutation (g*h)) p.spin) =
      ((H.permutation g) ((H.permutation h) p.natural),
       (H.permutation g) ((H.permutation h) p.spin))
    rw [map_mul]
    rfl

/-- `H` supplies only geometry; the linear transport is constructed from it. -/
def transport (H : AxisTransportData) (g : N) (p : Slot) :
    GeometricTransport p (slotPermutation H g p) where
  ambient := g.val
  natural_halfspaces := H.halfspaces g p.natural
  spin_halfspaces := H.halfspaces g p.spin
  pairing a := by
    have he := congrArg (fun n : N => n * g) (H.conjugate_k g p.natural)
    have hh : g * axisK p.natural = axisK (H.permutation g p.natural) * g := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using he
    exact congrArg (fun n : N => n.val a) hh
  signs a := by
    have he := congrArg (fun n : N => n * g) (H.conjugate_z g p.natural)
    have hh : g * axisZ p.natural = axisZ (H.permutation g p.natural) * g := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using he
    exact congrArg (fun n : N => n.val a) hh

/-- All Parker parameters are transported by the actual ambient permutation. -/
theorem transport_signed (H : AxisTransportData) (g : N) (p : Slot)
    (ε : ParkerBit) (x : Omega) (b : ParkerLoop) :
    (transport H g p).tensor (Natural.L p.natural ε x ⊗ₜ[ℝ] delta p b) =
      Natural.L (H.permutation g p.natural) ((transport H g p).label (x,ε)).2
        ((transport H g p).label (x,ε)).1 ⊗ₜ[ℝ]
          delta (slotPermutation H g p) ((transport H g p).loop b) :=
  (transport H g p).tensor_signed ε x b

end Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction.SixTensor

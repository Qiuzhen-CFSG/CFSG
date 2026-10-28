module

public import Theory.Representation.SymplecticNatural
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases

/-!
# The standard isotropic flag in symplectic four-space

The point is the span of e₀ and the plane is the span of e₀,e₁ in the
matrix model with ordered hyperbolic halves. Their stabilizers are the two
incident parabolics. Coordinate tests are obtained by checking the images of
the spanning vectors; finite dimension turns containment into equality.

The carrier and form convention agree with the Atlas-port symplectic model;
this module uses the module-compatible natural representation directly.

Source: the standard symplectic flag realization of the amalgam in
Aschbacher--Smith, F.1.12(I)(2), printed pp.262--264.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour

abbrev Vector (F : Type*) := (Fin 2 ⊕ Fin 2) → F
abbrev Sp (F : Type*) [CommRing F] := Matrix.symplecticGroup (Fin 2) F

variable (F : Type*) [Field F]

/-- The standard alternating form, with positive eᵢ,fᵢ pairing. -/
def form : LinearMap.BilinForm F (Vector F) := (-Matrix.J (Fin 2) F).toBilin'

variable {F} in
theorem form_apply (x y : Vector F) :
    form F x y = ∑ i : Fin 2, (x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i)) := by
  simp [form, Matrix.toBilin'_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply,
    Fintype.sum_sum_type, sub_eq_add_neg, Finset.sum_add_distrib, add_comm]

variable {F} in
def e (i : Fin 2) : Vector F := Pi.single (.inl i) 1

variable {F} in
@[simp] theorem form_e_right (x : Vector F) (i : Fin 2) :
    form F x (e i) = -x (.inr i) := by
  fin_cases i <;> simp [form_apply, e]

variable {F} in
/-- The invertible natural matrix representation. -/
def toLinear : Sp F →* (Vector F ≃ₗ[F] Vector F) where
  toFun g := LinearEquiv.ofBijective (Representation.symplecticNatural 2 g)
    ((Representation.symplecticNatural 2).apply_bijective g)
  map_one' := by ext x : 1; exact congrArg (fun f => f x) (Representation.symplecticNatural 2).map_one
  map_mul' g h := by ext x : 1; exact congrArg (fun f => f x) ((Representation.symplecticNatural 2).map_mul g h)

variable {F} in
@[simp] theorem toLinear_apply (g : Sp F) (x : Vector F) : toLinear g x = g • x := rfl

variable {F} in
theorem smul_eq_mulVec (g : Sp F) (x : Vector F) : g • x = g.val *ᵥ x := rfl

variable {F} in
/-- The carrier preserves the displayed form by its defining matrix equation. -/
theorem preserves_form (g : Sp F) (x y : Vector F) :
    form F (g • x) (g • y) = form F x y := by
  have hg := SymplecticGroup.mem_iff'.mp g.property
  have hm : g.valᵀ * (-Matrix.J (Fin 2) F) * g.val = -Matrix.J (Fin 2) F := by
    simp [hg]
  have h := Matrix.toBilin'_comp (-Matrix.J (Fin 2) F) g.val g.val
  rw [hm] at h
  exact congrArg (fun B : LinearMap.BilinForm F (Vector F) => B x y) h

/-- The isotropic point spanned by the first standard vector. -/
def point : Submodule F (Vector F) := F ∙ e 0

/-- The maximal isotropic plane: the second hyperbolic half vanishes. -/
def plane : Submodule F (Vector F) where
  carrier := {x | ∀ i, x (.inr i) = 0}
  zero_mem' := by simp
  add_mem' hx hy i := by simp [hx i, hy i]
  smul_mem' a x hx i := by simp [hx i]

variable {F}

@[simp] theorem mem_plane (x : Vector F) :
    x ∈ plane F ↔ ∀ i, x (.inr i) = 0 := Iff.rfl

@[simp] theorem e_mem_plane (i : Fin 2) : e i ∈ plane F := by
  simp [mem_plane, e]

theorem point_le_plane : point F ≤ plane F := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact e_mem_plane 0

theorem point_isotropic (x y : Vector F) (hx : x ∈ point F) (hy : y ∈ point F) :
    form F x y = 0 := by
  have hx' := point_le_plane hx
  have hy' := point_le_plane hy
  simp [form_apply, (mem_plane x).mp hx', (mem_plane y).mp hy']

theorem plane_isotropic (x y : Vector F) (hx : x ∈ plane F) (hy : y ∈ plane F) :
    form F x y = 0 := by
  simp [form_apply, (mem_plane x).mp hx, (mem_plane y).mp hy]

/-- The orthogonal complement of the displayed plane is itself. -/
theorem orthogonal_plane_iff (x : Vector F) :
    (∀ y ∈ plane F, form F x y = 0) ↔ x ∈ plane F := by
  constructor
  · intro h i
    simpa using h (e i) (e_mem_plane i)
  · intro hx y hy
    exact plane_isotropic x y hx hy

/-- Concrete coordinates on the plane. -/
def planeEquiv : plane F ≃ₗ[F] (Fin 2 → F) where
  toFun x i := x.val (.inl i)
  invFun x := ⟨Sum.elim x 0, by intro i; rfl⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact (x.property i).symm
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_plane : Module.finrank F (plane F) = 2 := by
  rw [planeEquiv.finrank_eq]
  simp

theorem finrank_point : Module.finrank F (point F) = 1 := by
  apply finrank_span_singleton
  intro h
  have := congrFun h (.inl 0)
  simp [e] at this

theorem point_lt_plane : point F < plane F := by
  refine lt_of_le_of_ne point_le_plane ?_
  intro h
  have := congrArg (fun W : Submodule F (Vector F) => Module.finrank F W) h
  rw [finrank_point, finrank_plane] at this
  contradiction

theorem mem_point_iff (x : Vector F) :
    x ∈ point F ↔ x (.inl 1) = 0 ∧ ∀ i, x (.inr i) = 0 := by
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [e]
  · rintro ⟨h₁, h₂⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x (.inl 0), ?_⟩
    funext i
    cases i with
    | inl i => fin_cases i <;> simp [e, h₁]
    | inr i => simp [e, h₂ i]

theorem plane_decomposition (x : Vector F) (hx : x ∈ plane F) :
    x = x (.inl 0) • e 0 + x (.inl 1) • e 1 := by
  funext i
  cases i with
  | inl i => fin_cases i <;> simp [e]
  | inr i => simp [e, hx i]

/-- Setwise subspace stabilizer under the actual matrix action. -/
def stabilizer (W : Submodule F (Vector F)) : Subgroup (Sp F) :=
  (MulAction.stabilizer (Vector F ≃ₗ[F] Vector F) W).comap toLinear

/-- In finite dimension it suffices to check forward invariance. -/
theorem mem_stabilizer_iff (W : Submodule F (Vector F)) (g : Sp F) :
    g ∈ stabilizer W ↔ ∀ x ∈ W, g • x ∈ W := by
  change W.map (toLinear g).toLinearMap = W ↔ _
  constructor
  · intro h x hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro h
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro y ⟨x, hx, rfl⟩
      exact h x hx
    · exact (toLinear g).finrank_map_eq W

/-- The point parabolic. -/
def pointParabolic : Subgroup (Sp F) := stabilizer (point F)

/-- The plane parabolic. -/
def planeParabolic : Subgroup (Sp F) := stabilizer (plane F)

/-- The whole flag overlap, retaining its torus. -/
def borel : Subgroup (Sp F) := pointParabolic ⊓ planeParabolic

theorem mem_pointParabolic_iff (g : Sp F) :
    g ∈ pointParabolic ↔
      g.val (.inl 1) (.inl 0) = 0 ∧ ∀ i, g.val (.inr i) (.inl 0) = 0 := by
  rw [pointParabolic, mem_stabilizer_iff]
  constructor
  · intro h
    have he : e (F := F) 0 ∈ point F := Submodule.subset_span (by simp)
    simpa [mem_point_iff, smul_eq_mulVec, e, Matrix.mulVec_single] using h (e 0) he
  · intro h x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have he : g • e 0 ∈ point F := by
      simpa [mem_point_iff, smul_eq_mulVec, e, Matrix.mulVec_single] using h
    change toLinear g (a • e 0) ∈ point F
    rw [map_smul]
    exact (point F).smul_mem a he

theorem mem_planeParabolic_iff (g : Sp F) :
    g ∈ planeParabolic ↔ ∀ i j, g.val (.inr i) (.inl j) = 0 := by
  rw [planeParabolic, mem_stabilizer_iff]
  constructor
  · intro h i j
    have he := h (e j) (e_mem_plane j)
    simpa [smul_eq_mulVec, e, Matrix.mulVec_single] using he i
  · intro h x hx
    rw [plane_decomposition x hx]
    change toLinear g (_ + _) ∈ plane F
    rw [map_add, map_smul, map_smul]
    apply (plane F).add_mem
    · apply (plane F).smul_mem
      intro i
      simpa [toLinear_apply, smul_eq_mulVec, e, Matrix.mulVec_single] using h i 0
    · apply (plane F).smul_mem
      intro i
      simpa [toLinear_apply, smul_eq_mulVec, e, Matrix.mulVec_single] using h i 1

theorem mem_borel_iff (g : Sp F) :
    g ∈ borel ↔ g.val (.inl 1) (.inl 0) = 0 ∧
      ∀ i j, g.val (.inr i) (.inl j) = 0 := by
  change (g ∈ pointParabolic ∧ g ∈ planeParabolic) ↔ _
  rw [mem_pointParabolic_iff, mem_planeParabolic_iff]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun i => h.2 i 0⟩, h.2⟩⟩

end Theory.SpecificGroups.SymplecticFour

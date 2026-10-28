module

public import Theory.Representation.BinaryNaturalDual.Action

/-!
# Pairing-one stabilizers and their complementary modules

A vector and covector paired to one split the natural space as their marked
line plus the covector kernel. Restriction identifies their simultaneous
stabilizer with the full linear group of that kernel. Restriction of covectors
identifies the complementary annihilator with the kernel dual and intertwines
the actual contragredient actions.

The inverse group map extends a kernel automorphism by the identity on the
marked line, using the explicit projection `v ↦ v - f(v)x`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(4),
printed p.390. These calculations are independent of any Sylow marking.
-/

@[expose] public section

namespace BinaryNaturalDual.VectorStabilizers
open BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Evaluation at a marked vector, as a functional on the dual space. -/
def evaluationAt (x : V) : Module.Dual (ZMod 2) V →ₗ[ZMod 2] ZMod 2 where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Covectors annihilating the marked vector. -/
def annihilator (x : V) : Submodule (ZMod 2) (Module.Dual (ZMod 2) V) :=
  (evaluationAt x).ker

@[simp] theorem mem_annihilator (x : V) (f : Module.Dual (ZMod 2) V) :
    f ∈ annihilator x ↔ f x = 0 := Iff.rfl

variable {x : V} {f : Module.Dual (ZMod 2) V}

theorem vector_ne_zero (h : f x = 1) : x ≠ 0 := by
  intro hx
  simp [hx] at h

theorem covector_ne_zero (h : f x = 1) : f ≠ 0 := by
  intro hf
  simp [hf] at h

/-- The projection along the marked line onto the kernel of its paired functional. -/
def kernelProjection (h : f x = 1) : V →ₗ[ZMod 2] f.ker :=
  (LinearMap.id - f.smulRight x).codRestrict f.ker (by
    intro v
    change f (v - f v • x) = 0
    simp [h])

@[simp] theorem kernelProjection_apply (h : f x = 1) (v : V) :
    (kernelProjection h v : V) = v - f v • x := rfl

/-- Coordinates for the direct sum of a pairing-one line and a hyperplane. -/
def pairCoordinates (h : f x = 1) : V ≃ₗ[ZMod 2] (ZMod 2 × f.ker) where
  toFun v := (f v, kernelProjection h v)
  invFun v := v.1 • x + v.2
  left_inv v := by simp
  right_inv v := by
    apply Prod.ext
    · change f (v.1 • x + v.2) = v.1
      simp [h, show f v.2 = 0 from v.2.property]
    · apply Subtype.ext
      change v.1 • x + v.2 - f (v.1 • x + v.2) • x = v.2
      simp [h, show f v.2 = 0 from v.2.property]
  map_add' v w := by simp only [map_add, Prod.mk_add_mk]
  map_smul' a v := by simp only [map_smul, RingHom.id_apply, Prod.smul_mk]

@[simp] theorem pairCoordinates_fst (h : f x = 1) (v : V) :
    (pairCoordinates h v).1 = f v := rfl

@[simp] theorem pairCoordinates_snd (h : f x = 1) (v : V) :
    (pairCoordinates h v).2 = kernelProjection h v := rfl

@[simp] theorem pairCoordinates_symm_apply (h : f x = 1) (a : ZMod 2) (w : f.ker) :
    (pairCoordinates h).symm (a,w) = a • x + w := rfl

/-- The summands in the nonsingular-vector decomposition are actual complements. -/
theorem line_isCompl_kernel (h : f x = 1) :
    IsCompl (Submodule.span (ZMod 2) {x}) f.ker := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro v hv hf
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have ha : a = 0 := by simpa [h] using hf
    simp [ha]
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    apply Submodule.mem_sup.mpr
    exact ⟨f v • x, Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton x)),
      kernelProjection h v, (kernelProjection h v).property, by simp⟩

/-- The dual decomposition uses exactly the annihilator of the marked vector. -/
theorem dual_line_isCompl_annihilator (h : f x = 1) :
    IsCompl (Submodule.span (ZMod 2) {f}) (annihilator x) :=
  line_isCompl_kernel (x := f) (f := evaluationAt x) h

/-- Restriction identifies the complementary covectors with the dual of the kernel. -/
def annihilatorEquivKernelDual (h : f x = 1) :
    annihilator x ≃ₗ[ZMod 2] Module.Dual (ZMod 2) f.ker where
  toFun q := q.val.comp f.ker.subtype
  invFun q := ⟨q.comp (kernelProjection h), by
    change q (kernelProjection h x) = 0
    have hx : kernelProjection h x = 0 := by apply Subtype.ext; simp [h]
    rw [hx, map_zero]⟩
  left_inv q := by
    apply Subtype.ext
    ext v
    change q.val (v - f v • x) = q.val v
    simp [show q.val x = 0 from q.property]
  right_inv q := by
    ext v
    change q (kernelProjection h v) = q v
    congr 1
    apply Subtype.ext
    simp [show f v = 0 from v.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem annihilatorEquivKernelDual_apply (h : f x = 1)
    (q : annihilator x) (w : f.ker) : annihilatorEquivKernelDual h q w = q.val w := rfl

theorem finrank_kernel [FiniteDimensional (ZMod 2) V] (h : f x = 1) :
    Module.finrank (ZMod 2) f.ker + 1 = Module.finrank (ZMod 2) V :=
  Module.Dual.finrank_ker_add_one_of_ne_zero (covector_ne_zero h)

theorem finrank_annihilator [FiniteDimensional (ZMod 2) V] (h : f x = 1) :
    Module.finrank (ZMod 2) (annihilator x) + 1 = Module.finrank (ZMod 2) V := by
  rw [(annihilatorEquivKernelDual h).finrank_eq, Subspace.dual_finrank_eq]
  exact finrank_kernel h

end BinaryNaturalDual.VectorStabilizers

namespace BinaryNaturalDual.VectorStabilizers
open BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The subgroup fixing a vector and its paired covector. -/
def pairStabilizer (x : V) (f : Module.Dual (ZMod 2) V) : Subgroup (BinaryLinear.GL V) where
  carrier := {g | g x = x ∧ ∀ v, f (g v) = f v}
  one_mem' := ⟨rfl, fun _ => rfl⟩
  mul_mem' := by
    intro g k hg hk
    exact ⟨by change g (k x) = x; rw [hk.1, hg.1], fun v => (hg.2 (k v)).trans (hk.2 v)⟩
  inv_mem' := by
    intro g hg
    refine ⟨?_, ?_⟩
    · apply g.injective
      simpa using hg.1.symm
    · intro v
      simpa using (hg.2 (g.symm v)).symm

@[simp] theorem mem_pairStabilizer (x : V) (f : Module.Dual (ZMod 2) V) (g : BinaryLinear.GL V) :
    g ∈ pairStabilizer x f ↔ g x = x ∧ ∀ v, f (g v) = f v := Iff.rfl

/-- This subgroup is the actual fixer for the natural-plus-contragredient action. -/
theorem mem_pairStabilizer_iff_action (x : V) (f : Module.Dual (ZMod 2) V) (g : BinaryLinear.GL V) :
    g ∈ pairStabilizer x f ↔ naturalDualRepresentation g (x, f) = (x, f) := by
  rw [naturalDualRepresentation_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨hx, hf⟩
    refine ⟨hx, ?_⟩
    ext v
    exact (show f (g (g.symm v)) = f (g.symm v) from hf (g.symm v)).symm.trans
      (by rw [g.apply_symm_apply])
  · rintro ⟨hx, hf⟩
    refine ⟨hx, fun v => ?_⟩
    have hh := LinearMap.congr_fun hf (g v)
    change f (g.symm (g v)) = f (g v) at hh
    simpa using hh.symm

/-- Restriction of the actual stabilizer action to the kernel. -/
def kernelAction (x : V) (f : Module.Dual (ZMod 2) V) :
    pairStabilizer x f →* BinaryLinear.GL f.ker where
  toFun g := {
    toFun v := ⟨g.val v, by change f (g.val v) = 0; rw [g.property.2]; exact v.property⟩
    invFun v := ⟨g.val.symm v, by
      have h := (g⁻¹).property.2 v
      change f (g.val.symm v) = 0
      exact h.trans v.property⟩
    left_inv v := Subtype.ext (g.val.symm_apply_apply v)
    right_inv v := Subtype.ext (g.val.apply_symm_apply v)
    map_add' _ _ := Subtype.ext (map_add _ _ _)
    map_smul' _ _ := Subtype.ext (map_smul _ _ _) }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp] theorem kernelAction_apply (x : V) (f : Module.Dual (ZMod 2) V)
    (g : pairStabilizer x f) (v : f.ker) :
    (kernelAction x f g v : V) = g.val v := rfl

variable {x : V} {f : Module.Dual (ZMod 2) V}

/-- Extend a kernel automorphism by the identity on the marked line. -/
def extendKernel (h : f x = 1) (k : BinaryLinear.GL f.ker) : BinaryLinear.GL V :=
  ((pairCoordinates h).trans ((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr k)).trans
    (pairCoordinates h).symm

@[simp] theorem extendKernel_apply (h : f x = 1) (k : BinaryLinear.GL f.ker) (v : V) :
    extendKernel h k v = f v • x + (k (kernelProjection h v) : V) := rfl

theorem extendKernel_mem (h : f x = 1) (k : BinaryLinear.GL f.ker) :
    extendKernel h k ∈ pairStabilizer x f := by
  constructor
  · rw [extendKernel_apply, h, one_smul]
    have hz : kernelProjection h x = 0 := by apply Subtype.ext; simp [h]
    simp [hz]
  · intro v
    rw [extendKernel_apply, map_add, map_smul, h, smul_eq_mul, mul_one]
    rw [show f (k (kernelProjection h v) : V) = 0 from (k (kernelProjection h v)).property,
      add_zero]

/-- The pairing-one stabilizer is the full linear group on the kernel,
with the isomorphism given by restriction, rather than by an order comparison. -/
def pairStabilizerEquivKernel (h : f x = 1) : pairStabilizer x f ≃* BinaryLinear.GL f.ker where
  toFun := kernelAction x f
  invFun k := ⟨extendKernel h k, extendKernel_mem h k⟩
  left_inv g := by
    apply Subtype.ext
    ext v
    change f v • x + g.val (v - f v • x) = g.val v
    rw [map_sub, map_smul, g.property.1]
    abel
  right_inv k := by
    ext v
    change f v • x + (k (kernelProjection h v) : V) = k v
    have hz : f v = 0 := v.property
    have hp : kernelProjection h v = v := by apply Subtype.ext; simp [hz]
    simp [hz, hp]
  map_mul' := (kernelAction x f).map_mul

@[simp] theorem pairStabilizerEquivKernel_apply (h : f x = 1)
    (g : pairStabilizer x f) (v : f.ker) :
    (pairStabilizerEquivKernel h g v : V) = g.val v := rfl

/-- The kernel projection commutes with the stabilizer action. -/
theorem kernelProjection_equivariant (h : f x = 1) (g : pairStabilizer x f) (v : V) :
    kernelProjection h (g.val v) = kernelAction x f g (kernelProjection h v) := by
  apply Subtype.ext
  change g.val v - f (g.val v) • x = g.val (v - f v • x)
  rw [g.property.2, map_sub, map_smul, g.property.1]

/-- The contragredient action preserves the complementary annihilator. -/
def annihilatorAction (x : V) (f : Module.Dual (ZMod 2) V)
    (g : pairStabilizer x f) (q : annihilator x) : annihilator x :=
  ⟨g.val.symm.dualMap q.val, by
    change q.val (g.val.symm x) = 0
    rw [show g.val.symm x = x from (g⁻¹).property.1]
    exact q.property⟩

/-- Restriction to the kernel intertwines the annihilator action with the
exact dual of the kernel action. -/
theorem annihilatorEquivKernelDual_equivariant (h : f x = 1)
    (g : pairStabilizer x f) (q : annihilator x) :
    annihilatorEquivKernelDual h (annihilatorAction x f g q) =
      (kernelAction x f g).symm.dualMap (annihilatorEquivKernelDual h q) := by
  ext w
  rfl

end BinaryNaturalDual.VectorStabilizers

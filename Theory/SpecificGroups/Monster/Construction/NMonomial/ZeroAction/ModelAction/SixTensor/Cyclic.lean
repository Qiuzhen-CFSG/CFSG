module
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.ModelAction.SixTensor.Transport

/-!
# Marked cyclic relabellings of the six source factors

The actual cyclic permutation of Parker triples carries both halfspace
families and conjugates each literal orbit and sign involution to its next
index. Its tensor transport agrees with the marked parameter-preserving
relabelling. These relabellings compose coherently, their inverse conventions
are explicit, and they preserve the tensor forms.

The source's preferred factors are `(2,0)`, `(0,1)`, `(1,2)`. The three
published literal factors are compared by marked tensor equivalences. The
coordinate-dependent partner comparisons between the two orientations are a
separate construction; a cyclic relabelling does not replace that correction.

Source: Aschbacher, *Sporadic Groups*, 14.2.1 (printed p. 59), Section 27,
and 29.7(1), 29.7.5 (printed pp. 156–157).
-/

@[expose] public section
noncomputable section
open Atlas.Fischer Atlas.Codes
open Sporadic.Monster.Construction.TrialitySpin
open SignedModules SpinActions
open scoped TensorProduct
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction.SixTensor

/-- Relabelling retains both the Parker parameter and the central orbit convention. -/
def relabel (p q : Slot) (h : twist p = twist q) : Tensor p ≃ₗ[ℝ] Tensor q :=
  TensorProduct.congr (LinearEquiv.refl ℝ (Natural.Space p.natural))
    (spinComparison p (realization q.spin (twist q)) h)

@[simp] theorem relabel_marked (p q : Slot) (h : twist p = twist q)
    (x : Omega) (b : ParkerLoop) : relabel p q h (marked p x b) = marked q x b := by
  change Natural.L p.natural 1 x ⊗ₜ[ℝ]
    spinComparison p (realization q.spin (twist q)) h (delta p b) = _
  exact congrArg (fun s : Spin q => Natural.L q.natural 1 x ⊗ₜ[ℝ] s)
    (spinComparison_delta p (realization q.spin (twist q)) h b)

theorem relabel_isometry (p q : Slot) (h : twist p = twist q) (v w : Tensor p) :
    tensorForm q (relabel p q h v) (relabel p q h w) = tensorForm p v w := by
  have he : (tensorForm q).compl₁₂ (relabel p q h).toLinearMap
      (relabel p q h).toLinearMap = tensorForm p := by
    apply TensorProduct.ext'
    intro a s
    apply TensorProduct.ext'
    intro b t
    change (Natural.form q.natural).tmul (spinForm q)
      (a ⊗ₜ[ℝ] spinComparison p (realization q.spin (twist q)) h s)
      (b ⊗ₜ[ℝ] spinComparison p (realization q.spin (twist q)) h t) = _
    simp only [tensorForm, LinearMap.BilinForm.tensorDistrib_tmul]
    rw [show spinForm q (spinComparison p (realization q.spin (twist q)) h s)
        (spinComparison p (realization q.spin (twist q)) h t) = spinForm p s t from
      spinComparison_isometry p (realization q.spin (twist q)) h s t]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun he v) w

@[simp] theorem relabel_refl (p : Slot) : relabel p p rfl = LinearEquiv.refl ℝ (Tensor p) := by
  apply LinearEquiv.toLinearMap_injective
  apply marked_ext p
  intro x b
  exact relabel_marked p p rfl x b

theorem relabel_trans (p q r : Slot) (h : twist p = twist q) (k : twist q = twist r) :
    (relabel p q h).trans (relabel q r k) = relabel p r (h.trans k) := by
  apply LinearEquiv.toLinearMap_injective
  apply marked_ext p
  intro x b
  change relabel q r k (relabel p q h (marked p x b)) = relabel p r _ (marked p x b)
  rw [relabel_marked, relabel_marked, relabel_marked]

@[simp] theorem relabel_symm (p q : Slot) (h : twist p = twist q) :
    (relabel p q h).symm = relabel q p h.symm := by
  apply LinearEquiv.toLinearMap_injective
  apply marked_ext q
  intro x b
  apply (relabel p q h).injective
  change relabel p q h ((relabel p q h).symm (marked q x b)) =
    relabel p q h (relabel q p h.symm (marked q x b))
  rw [LinearEquiv.apply_symm_apply, relabel_marked, relabel_marked]

/-- The cyclic permutation from source 14.2.1: `0 → 1 → 2 → 0`. -/
def next : Equiv.Perm Natural.Axis where
  toFun i := i + 1
  invFun i := i + 2
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def rotate : Equiv.Perm Slot := slotPerm next

@[simp] theorem rotate_natural (p : Slot) : (rotate p).natural = next p.natural := rfl
@[simp] theorem rotate_spin (p : Slot) : (rotate p).spin = next p.spin := rfl

@[simp] theorem rotate_twist (p : Slot) : twist (rotate p) = twist p := by
  rcases p with ⟨⟨j,i⟩,h⟩
  fin_cases j <;> fin_cases i <;> rfl

@[simp] theorem cycle_point (i : Natural.Axis) (b : ParkerLoop) :
    cycle (Natural.point i b) = Natural.point (next i) b := by fin_cases i <;> rfl

/-- The cyclic relabelling is certified on actual halfspace subsets. -/
theorem cycle_halfspace (i : Natural.Axis) (l : Natural.Label) :
    cycle '' Natural.halfspace i l = Natural.halfspace (next i) l := by
  change cycle '' (Natural.point i '' _) = Natural.point (next i) '' _
  rw [Set.image_image]
  congr 1
  funext b
  exact cycle_point i b

theorem cycle_axisK (i : Natural.Axis) (a : Triple) :
    cycle ((axisK i).val a) = (axisK (next i)).val (cycle a) := by
  rcases a with ⟨a,b,c⟩
  fin_cases i <;> simp [axisK, next, cycle, k1_apply, k2_apply, k3_on_triple]

theorem cycle_axisZ (i : Natural.Axis) (a : Triple) :
    cycle ((axisZ i).val a) = (axisZ (next i)).val (cycle a) := by
  rcases a with ⟨a,b,c⟩
  fin_cases i
  · exact congrArg cycle (z1_apply a b c) |>.trans (z2_apply c a b).symm
  · exact congrArg cycle (z2_apply a b c) |>.trans (z3_apply c a b).symm
  · exact congrArg cycle (z3_apply a b c) |>.trans (z1_apply c a b).symm

/-- The cyclic map is induced by the actual triple permutation, without an N-membership premise. -/
def cycleTransport (p : Slot) : GeometricTransport p (rotate p) where
  ambient := cycle
  natural_halfspaces l := ⟨l,cycle_halfspace p.natural l⟩
  spin_halfspaces l := ⟨l,cycle_halfspace p.spin l⟩
  pairing := cycle_axisK p.natural
  signs := cycle_axisZ p.natural

theorem cycleTransport_marked (p : Slot) (x : Omega) (b : ParkerLoop) :
    (cycleTransport p).tensor (marked p x b) = marked (rotate p) x b :=
  (cycleTransport p).tensor_of_images 1 1 x x b b
    (cycle_halfspace p.natural (x,1)) (cycle_point p.spin b)

/-- Agreement with actual cyclic geometry, not just an equality of carriers. -/
theorem cycleTransport_eq_relabel (p : Slot) :
    (cycleTransport p).tensor = relabel p (rotate p) (rotate_twist p).symm := by
  apply LinearEquiv.toLinearMap_injective
  apply marked_ext p
  intro x b
  exact (cycleTransport_marked p x b).trans (relabel_marked p (rotate p) _ x b).symm

@[simp] theorem rotate_slot20 : rotate slot20 = slot01 := rfl
@[simp] theorem rotate_slot01 : rotate slot01 = slot12 := rfl
@[simp] theorem rotate_slot12 : rotate slot12 = slot20 := rfl
@[simp] theorem rotate_slot02 : rotate slot02 = slot10 := rfl
@[simp] theorem rotate_slot10 : rotate slot10 = slot21 := rfl
@[simp] theorem rotate_slot21 : rotate slot21 = slot02 := rfl

/-- The three marked comparisons with the already published tensor factors. -/
def tensorToB1A2 : Tensor slot01 ≃ₗ[ℝ] (Natural.B1_24 ⊗[ℝ] B1A2) :=
  TensorProduct.congr (LinearEquiv.refl ℝ Natural.B1_24) toB1A2

def tensorToB3A2 : Tensor slot21 ≃ₗ[ℝ] (Natural.B3_24 ⊗[ℝ] B3A2) :=
  TensorProduct.congr (LinearEquiv.refl ℝ Natural.B3_24) toB3A2

def tensorToB1A3 : Tensor slot02 ≃ₗ[ℝ] (Natural.B1_24 ⊗[ℝ] B1A3) :=
  TensorProduct.congr (LinearEquiv.refl ℝ Natural.B1_24) toB1A3

@[simp] theorem tensorToB1A2_marked (x : Omega) (b : ParkerLoop) :
    tensorToB1A2 (marked slot01 x b) = Natural.L 0 1 x ⊗ₜ[ℝ] delta2 b := by
  change Natural.L 0 1 x ⊗ₜ[ℝ] toB1A2 (delta slot01 b) = _
  rw [toB1A2_delta]

@[simp] theorem tensorToB3A2_marked (x : Omega) (b : ParkerLoop) :
    tensorToB3A2 (marked slot21 x b) = Natural.L 2 1 x ⊗ₜ[ℝ] B3Axis2.delta b := by
  change Natural.L 2 1 x ⊗ₜ[ℝ] toB3A2 (delta slot21 b) = _
  rw [toB3A2_delta]

@[simp] theorem tensorToB1A3_marked (x : Omega) (b : ParkerLoop) :
    tensorToB1A3 (marked slot02 x b) = Natural.L 0 1 x ⊗ₜ[ℝ] delta3 b := by
  change Natural.L 0 1 x ⊗ₜ[ℝ] toB1A3 (delta slot02 b) = _
  rw [toB1A3_delta]

/-- The source's preferred orientation, indexed by its Parker axis. -/
def preferred (i : Natural.Axis) : Slot := ⟨(i + 2,i), by fin_cases i <;> decide⟩

/-- The other orientation on the same Parker axis. -/
def alternate (i : Natural.Axis) : Slot := ⟨(i + 1,i), by fin_cases i <;> decide⟩

@[simp] theorem preferred_spin (i : Natural.Axis) : (preferred i).spin = i := rfl
@[simp] theorem alternate_spin (i : Natural.Axis) : (alternate i).spin = i := rfl
@[simp] theorem preferred_twist (i : Natural.Axis) : twist (preferred i) = 0 := by
  fin_cases i <;> rfl
@[simp] theorem alternate_twist (i : Natural.Axis) : twist (alternate i) = 1 := by
  fin_cases i <;> rfl

@[simp] theorem preferred_zero : preferred 0 = slot20 := rfl
@[simp] theorem preferred_one : preferred 1 = slot01 := rfl
@[simp] theorem preferred_two : preferred 2 = slot12 := rfl
@[simp] theorem alternate_zero : alternate 0 = slot10 := rfl
@[simp] theorem alternate_one : alternate 1 = slot21 := rfl
@[simp] theorem alternate_two : alternate 2 = slot02 := rfl

/-- Every ordered pair belongs to exactly one of the two displayed cyclic families. -/
theorem eq_preferred_or_alternate (p : Slot) :
    p = preferred p.spin ∨ p = alternate p.spin := by
  rcases p with ⟨⟨j,i⟩,h⟩
  fin_cases j <;> fin_cases i
  all_goals try exact False.elim (h rfl)
  all_goals first | exact Or.inl (Subtype.ext rfl) | exact Or.inr (Subtype.ext rfl)

end Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction.SixTensor

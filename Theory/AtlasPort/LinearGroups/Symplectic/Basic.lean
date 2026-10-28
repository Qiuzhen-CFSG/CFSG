import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.SetTheory.Cardinal.Finite
set_option warningAsError false

/-! The primary matrix model and its alternating form, in every characteristic. -/
noncomputable section
namespace Atlas.Symplectic
open Matrix

abbrev Index (n : ℕ) := Fin n ⊕ Fin n
abbrev Vector (n : ℕ) (F : Type*) := Index n → F
abbrev Sp (n : ℕ) (F : Type*) [CommRing F] := ↥(Matrix.symplecticGroup (Fin n) F)
abbrev PSp (n : ℕ) (F : Type*) [CommRing F] := Sp n F ⧸ Subgroup.center (Sp n F)

def orderNumerator (n q : ℕ) : ℕ :=
  q ^ (n * n) * ∏ i ∈ Finset.range n, (q ^ (2 * (i + 1)) - 1)

def Good (n q : ℕ) : Prop := (n = 1 ∧ 3 < q) ∨ (2 ≤ n ∧ (n,q) ≠ (2,2))

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

instance rank_zero_subsingleton : Subsingleton (Sp 0 F) := inferInstance
instance rank_zero_projective_subsingleton : Subsingleton (PSp 0 F) := by
  constructor
  intro x y
  obtain ⟨a,rfl⟩ := projection_surjective x
  obtain ⟨b,rfl⟩ := projection_surjective y
  rw [Subsingleton.elim a b]

theorem card_rank_zero : Nat.card (Sp 0 F) = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
theorem card_projective_rank_zero : Nat.card (PSp 0 F) = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩

@[simp] theorem orderNumerator_zero (q : ℕ) : orderNumerator 0 q = 1 := by simp [orderNumerator]
end Atlas.Symplectic

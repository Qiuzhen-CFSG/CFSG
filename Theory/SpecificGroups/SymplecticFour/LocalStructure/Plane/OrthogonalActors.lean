module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-!
# Plane shears preserving a quadratic refinement

For a symmetric shear with entries x,y,z, preservation of a quadratic
refinement gives x = ax²+by² and z = ay²+bz². The scalar ax+bz is
idempotent. If either coefficient is nonzero, this scalar and one matrix
entry determine the whole shear; if both vanish, only y remains free.
There are therefore at most 2|F| actors, for either orthogonal type.

This is the finite orthogonal estimate in the first symplectic paragraph
of MS93 (3.3), printed p.867. At q=4 it excludes a plane actor of order
at least q². It does not assert that a source actor preserves a refinement.
-/

public section
noncomputable section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour.Plane
namespace OrthogonalActors
variable {F : Type*} [Field F] [CharP F 2]

/-- The coefficient equations forced by the two complementary basis vectors. -/
def Equations (a b : F) (B : symmetricMatrices F) : Prop :=
  B.val 0 0 = a * B.val 0 0 ^ 2 + b * B.val 0 1 ^ 2 ∧
  B.val 1 1 = a * B.val 0 1 ^ 2 + b * B.val 1 1 ^ 2

omit [CharP F 2] in
private theorem symmetric_ext {B C : symmetricMatrices F}
    (h00 : B.val 0 0 = C.val 0 0) (h01 : B.val 0 1 = C.val 0 1)
    (h11 : B.val 1 1 = C.val 1 1) : B = C := by
  apply Subtype.ext
  have hB : B.val 1 0 = B.val 0 1 := congrFun (congrFun B.property 0) 1
  have hC : C.val 1 0 = C.val 0 1 := congrFun (congrFun C.property 0) 1
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact hB.trans (h01.trans hC.symm)
  · exact h11

private theorem square_injective : Function.Injective (fun x : F => x^2) := by
  intro x y h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

private theorem idempotent {a b : F} {B : symmetricMatrices F}
    (h : Equations a b B) :
    (a*B.val 0 0+b*B.val 1 1)^2 = a*B.val 0 0+b*B.val 1 1 := by
  calc
    _ = a^2*B.val 0 0^2+b^2*B.val 1 1^2 := by
      simp only [CharTwo.add_sq, mul_pow]
    _ = a*(a*B.val 0 0^2+b*B.val 0 1^2)+
        b*(a*B.val 0 1^2+b*B.val 1 1^2) := by
      have hz : a*b*B.val 0 1^2+a*b*B.val 0 1^2 = 0 := CharTwo.add_self_eq_zero _
      calc
        _ = a^2*B.val 0 0^2+b^2*B.val 1 1^2+
            (a*b*B.val 0 1^2+a*b*B.val 0 1^2) := by rw [hz,add_zero]
        _ = _ := by ring
    _ = _ := by rw [←h.1,←h.2]

private def binaryCode (x : F) : Bool := by classical exact decide (x ≠ 0)

omit [CharP F 2] in
private theorem binaryCode_injective {x y : F} (hx : x^2=x) (hy : y^2=y)
    (he : binaryCode x = binaryCode y) : x=y := by
  rcases eq_zero_or_one_of_sq_eq_self hx with rfl | rfl <;>
    rcases eq_zero_or_one_of_sq_eq_self hy with rfl | rfl <;>
      simp_all [binaryCode]

variable [Finite F]

/-- All symmetric shears satisfying the orthogonal equations number at
most twice the field order. No choice of orthogonal type is required. -/
theorem card_equations_le (a b : F) :
    Nat.card {B : symmetricMatrices F // Equations a b B} ≤ 2*Nat.card F := by
  classical
  by_cases hb : b = 0
  · subst b
    by_cases ha : a = 0
    · subst a
      let f : {B : symmetricMatrices F // Equations 0 0 B} → F := fun B => B.val.val 0 1
      have hf : Function.Injective f := by
        intro B C he
        apply Subtype.ext
        apply symmetric_ext
        · have hB := B.property.1; have hC := C.property.1
          simp only [zero_mul,add_zero] at hB hC
          exact hB.trans hC.symm
        · exact he
        · have hB := B.property.2; have hC := C.property.2
          simp only [zero_mul,add_zero] at hB hC
          exact hB.trans hC.symm
      exact (Nat.card_le_card_of_injective f hf).trans (by omega)
    · let f : {B : symmetricMatrices F // Equations a 0 B} → F × Bool :=
        fun B => (B.val.val 1 1,binaryCode (a*B.val.val 0 0))
      have hf : Function.Injective f := by
        intro B C he
        have hz : B.val.val 1 1 = C.val.val 1 1 := congrArg Prod.fst he
        have hi : a*B.val.val 0 0 = a*C.val.val 0 0 := binaryCode_injective
          (by simpa using idempotent B.property)
          (by simpa using idempotent C.property) (congrArg Prod.snd he)
        have hx := (mul_left_cancel₀ ha hi)
        have hy : B.val.val 0 1 = C.val.val 0 1 := by
          apply square_injective
          apply mul_left_cancel₀ ha
          have hB := B.property.2; have hC := C.property.2
          simpa only [zero_mul,add_zero] using hB.symm.trans (hz.trans hC)
        exact Subtype.ext (symmetric_ext hx hy hz)
      have h := Nat.card_le_card_of_injective f hf
      simpa only [Nat.card_prod,show Nat.card Bool = 2 by simp,Nat.mul_comm] using h
  · let f : {B : symmetricMatrices F // Equations a b B} → F × Bool :=
      fun B => (B.val.val 0 0,binaryCode (a*B.val.val 0 0+b*B.val.val 1 1))
    have hf : Function.Injective f := by
      intro B C he
      have hx : B.val.val 0 0 = C.val.val 0 0 := congrArg Prod.fst he
      have hi := binaryCode_injective (idempotent B.property) (idempotent C.property)
        (congrArg Prod.snd he)
      have hz : B.val.val 1 1 = C.val.val 1 1 := by
        apply mul_left_cancel₀ hb
        rw [hx] at hi
        exact add_left_cancel hi
      have hy : B.val.val 0 1 = C.val.val 0 1 := by
        apply square_injective
        apply mul_left_cancel₀ hb
        have hh := B.property.1.symm.trans (hx.trans C.property.1)
        rw [hx] at hh
        exact add_left_cancel hh
      exact Subtype.ext (symmetric_ext hx hy hz)
    have h := Nat.card_le_card_of_injective f hf
    simpa only [Nat.card_prod,show Nat.card Bool = 2 by simp,Nat.mul_comm] using h

omit [Finite F] in
/-- Every quadratic refinement of the standard alternating form has these
diagonal coefficients. No restriction on its orthogonal type is imposed. -/
def refinement (c : Vector F) (v : Vector F) : F :=
  v (.inl 0)*v (.inr 0)+v (.inl 1)*v (.inr 1)+
    ∑ i, c i*v i^2

omit [Finite F] [CharP F 2] in
/-- Evaluation of the quadratic refinement in the fixed symplectic coordinates. -/
theorem refinement_apply (c v : Vector F) :
    refinement c v = v (.inl 0)*v (.inr 0)+v (.inl 1)*v (.inr 1)+
      ∑ i, c i*v i^2 := by rfl

omit [Finite F] in
/-- The actual natural shear action forces the two coefficient equations. -/
theorem equations_of_preserves (c : Vector F) (B : symmetricMatrices F)
    (h : ∀ v, refinement c (shearSp B • v) = refinement c v) :
    Equations (c (.inl 0)) (c (.inl 1)) B := by
  have hs : B.val 1 0 = B.val 0 1 := congrFun (congrFun B.property 0) 1
  have h0 := h (Pi.single (.inr 0) 1)
  have h1 := h (Pi.single (.inr 1) 1)
  simp only [smul_eq_mulVec, Matrix.mulVec_single] at h0 h1
  simp [refinement,shearSp,Matrix.fromBlocks,Matrix.one_apply,
    Fintype.sum_sum_type,Fin.sum_univ_two,Pi.single_apply,hs] at h0 h1
  constructor
  · change B.val 0 0 = c (.inl 0)*B.val 0 0^2+c (.inl 1)*B.val 0 1^2
    have hh : B.val 0 0 +
        (c (.inl 0)*B.val 0 0^2+c (.inl 1)*B.val 0 1^2) = 0 :=
      add_right_cancel (by simpa only [add_assoc,zero_add] using h0)
    exact (CharTwo.add_eq_zero).mp hh
  · change B.val 1 1 = c (.inl 0)*B.val 0 1^2+c (.inl 1)*B.val 1 1^2
    have hh : B.val 1 1 +
        (c (.inl 0)*B.val 0 1^2+c (.inl 1)*B.val 1 1^2) = 0 :=
      add_right_cancel (by simpa only [add_assoc,zero_add] using h1)
    exact (CharTwo.add_eq_zero).mp hh

/-- An actual subgroup of the plane radical preserving a quadratic
refinement has order at most 2q. -/
theorem card_radical_subgroup_le (A : Subgroup (radical (F := F)))
    (c : Vector F)
    (h : ∀ g : A, ∀ v, refinement c (g.val.val.val • v) = refinement c v) :
    Nat.card A ≤ 2*Nat.card F := by
  let f : A → {B : symmetricMatrices F // Equations (c (.inl 0)) (c (.inl 1)) B} :=
    fun g => ⟨(radicalEquiv g.val).toAdd,equations_of_preserves c _ (by
      have he : shearSp (radicalEquiv g.val).toAdd = g.val.val.val := by
        have he0 := congrArg (fun q : radical (F := F) => q.val.val)
          (radicalEquiv.left_inv g.val)
        have hs := congrArg (fun l : planeLocal (F := F) => l.val)
          (radicalEquiv_symm_val (radicalEquiv g.val))
        change (radicalEquiv.symm (radicalEquiv g.val)).val.val = _ at he0
        rw [hs] at he0
        exact he0
      rw [he]
      exact h g)⟩
  have hf : Function.Injective f := by
    intro g k he
    apply Subtype.ext
    apply radicalEquiv.injective
    apply Multiplicative.toAdd.injective
    exact congrArg Subtype.val he
  exact (Nat.card_le_card_of_injective f hf).trans (card_equations_le _ _)

/-- A quadratic plane actor of order at least sixteen cannot occur over a
four-element field. This is the numerical exclusion used in MS93 (3.3). -/
theorem not_card_ge_sixteen_of_card_four
    (hF : Nat.card F = 4) (A : Subgroup (radical (F := F)))
    (c : Vector F)
    (h : ∀ g : A, ∀ v, refinement c (g.val.val.val • v) = refinement c v)
    (hA : 16 ≤ Nat.card A) : False := by
  have hle := card_radical_subgroup_le A c h
  omega

end OrthogonalActors
end Theory.SpecificGroups.SymplecticFour.Plane

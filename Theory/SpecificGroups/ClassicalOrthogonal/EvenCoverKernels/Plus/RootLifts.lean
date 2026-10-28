module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.CentralCoprimeCardLift
public import Mathlib.Algebra.CharP.Two

/-!
# Canonical Siegel generators in odd central covers of split orthogonal groups

Every Siegel generator has square one in characteristic two. Across a central
kernel of odd order it therefore has a unique square-one lift. The lifts retain
addition of perpendicular parameters and every conjugation relation between
these generators. In a perfect cover they generate the whole covering group.

These are local lifting facts for the odd-primary part of GLS3 Section 6.1,
Theorem 6.1.4. They do not assert a presentation of the split orthogonal group
or exclude odd covering kernels. In particular they make no claim that the
identity cover of D₄(2) is universal. The concrete Siegel maps are those of
GLS3 Section 2.7 and `ClassicalOrthogonal.SplitOdd`.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.EvenCoverKernels.Plus
open Subgroup PerfectCentralCovering
universe u v
variable {F : Type u} [Field F] {r : ℕ}
variable {E : Type v} [Group E]

/-- A marked Siegel generator in the literal projective elementary carrier. -/
def siegelGenerator (u v : VectorD r F) (hu : formD r F u = 0)
    (hv : (formD r F).polarBilin u v = 0) : POmegaPlus r F :=
  projectiveElementaryMap (formD r F)
    ⟨siegelElement (formD r F) u v hu hv, siegelElement_mem _ _ _ _ _⟩

/-- Parameter addition holds before and after the scalar quotient. -/
theorem siegelGenerator_add (u v w : VectorD r F) (hu : formD r F u = 0)
    (hv : (formD r F).polarBilin u v = 0)
    (hw : (formD r F).polarBilin u w = 0) :
    siegelGenerator u v hu hv * siegelGenerator u w hu hw =
      siegelGenerator u (v + w) hu (by rw [map_add, hv, hw, add_zero]) := by
  unfold siegelGenerator
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact Quadratic.siegel_add (formD r F) u v w x hu hv hw

@[simp] theorem siegelGenerator_zero (u : VectorD r F) (hu : formD r F u = 0) :
    siegelGenerator u 0 hu (by simp) = 1 := by
  unfold siegelGenerator
  have h : (⟨siegelElement (formD r F) u 0 hu (by simp),
      siegelElement_mem _ _ _ _ _⟩ : OmegaPlus r F) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    exact Quadratic.siegel_zero (formD r F) u
  rw [h, map_one]

variable [CharP F 2]

/-- This uses characteristic two on the actual natural space. -/
theorem siegelGenerator_sq (u v : VectorD r F) (hu : formD r F u = 0)
    (hv : (formD r F).polarBilin u v = 0) :
    siegelGenerator u v hu hv ^ 2 = 1 := by
  rw [pow_two, siegelGenerator_add]
  have hvv : v + v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  simp only [hvv, siegelGenerator_zero]

/-- The unique square-one preimage of the specified Siegel generator. -/
def siegelLift (c : Cover E (POmegaPlus r F))
    (ho : Odd (Nat.card c.toMonoidHom.ker))
    (u v : VectorD r F) (hu : formD r F u = 0)
    (hv : (formD r F).polarBilin u v = 0) : E :=
  (c.toMonoidHom.exists_pow_eq_one_lift_of_central_coprime_ker c.surjective
    c.ker_le_center (Nat.coprime_two_right.mpr ho)
    (siegelGenerator u v hu hv) (siegelGenerator_sq u v hu hv)).choose

@[simp] theorem siegelLift_map (c : Cover E (POmegaPlus r F))
    (ho : Odd (Nat.card c.toMonoidHom.ker))
    (u v : VectorD r F) (hu : formD r F u = 0)
    (hv : (formD r F).polarBilin u v = 0) :
    c.toMonoidHom (siegelLift c ho u v hu hv) = siegelGenerator u v hu hv :=
  (c.toMonoidHom.exists_pow_eq_one_lift_of_central_coprime_ker c.surjective
    c.ker_le_center (Nat.coprime_two_right.mpr ho)
    (siegelGenerator u v hu hv) (siegelGenerator_sq u v hu hv)).choose_spec.1

@[simp] theorem siegelLift_sq (c : Cover E (POmegaPlus r F))
    (ho : Odd (Nat.card c.toMonoidHom.ker))
    (u v : VectorD r F) (hu : formD r F u = 0)
    (hv : (formD r F).polarBilin u v = 0) :
    siegelLift c ho u v hu hv ^ 2 = 1 :=
  (c.toMonoidHom.exists_pow_eq_one_lift_of_central_coprime_ker c.surjective
    c.ker_le_center (Nat.coprime_two_right.mpr ho)
    (siegelGenerator u v hu hv) (siegelGenerator_sq u v hu hv)).choose_spec.2

theorem siegelLift_unique (c : Cover E (POmegaPlus r F))
    (ho : Odd (Nat.card c.toMonoidHom.ker))
    (u v : VectorD r F) (hu : formD r F u = 0)
    (hv : (formD r F).polarBilin u v = 0) (x : E)
    (hx : c.toMonoidHom x = siegelGenerator u v hu hv) (hx2 : x ^ 2 = 1) :
    x = siegelLift c ho u v hu hv :=
  c.toMonoidHom.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker c.ker_le_center
    (Nat.coprime_two_right.mpr ho) (hx.trans (siegelLift_map c ho u v hu hv).symm)
    hx2 (siegelLift_sq c ho u v hu hv)

/-- Commuting base generators have commuting canonical lifts. -/
theorem siegelLift_commute (c : Cover E (POmegaPlus r F))
    (ho : Odd (Nat.card c.toMonoidHom.ker))
    (u v u' v' : VectorD r F) (hu : formD r F u = 0)
    (hv : (formD r F).polarBilin u v = 0) (hu' : formD r F u' = 0)
    (hv' : (formD r F).polarBilin u' v' = 0)
    (h : Commute (siegelGenerator u v hu hv) (siegelGenerator u' v' hu' hv')) :
    Commute (siegelLift c ho u v hu hv) (siegelLift c ho u' v' hu' hv') := by
  apply c.toMonoidHom.commute_of_map_commute_of_pow_eq_one_of_central_coprime_ker
    c.ker_le_center (Nat.coprime_two_right.mpr ho) (siegelLift_sq c ho u v hu hv)
  simpa only [siegelLift_map] using h

/-- Canonical lifts retain the full additive parameter subgroup. -/
theorem siegelLift_add (c : Cover E (POmegaPlus r F))
    (ho : Odd (Nat.card c.toMonoidHom.ker))
    (u v w : VectorD r F) (hu : formD r F u = 0)
    (hv : (formD r F).polarBilin u v = 0)
    (hw : (formD r F).polarBilin u w = 0) :
    siegelLift c ho u v hu hv * siegelLift c ho u w hu hw =
      siegelLift c ho u (v + w) hu (by rw [map_add, hv, hw, add_zero]) := by
  apply siegelLift_unique
  · rw [map_mul, siegelLift_map, siegelLift_map, siegelGenerator_add]
  · have h : Commute (siegelLift c ho u v hu hv) (siegelLift c ho u w hu hw) := by
      apply siegelLift_commute
      change _ * _ = _ * _
      simp only [siegelGenerator_add, add_comm v w]
    rw [h.mul_pow, siegelLift_sq, siegelLift_sq, mul_one]

/-- Conjugation relations descend and lift with the original marking. -/
theorem siegelLift_conjugate (c : Cover E (POmegaPlus r F))
    (ho : Odd (Nat.card c.toMonoidHom.ker)) (a : E)
    (u v u' v' : VectorD r F) (hu : formD r F u = 0)
    (hv : (formD r F).polarBilin u v = 0) (hu' : formD r F u' = 0)
    (hv' : (formD r F).polarBilin u' v' = 0)
    (h : c.toMonoidHom a * siegelGenerator u v hu hv * (c.toMonoidHom a)⁻¹ =
      siegelGenerator u' v' hu' hv') :
    a * siegelLift c ho u v hu hv * a⁻¹ = siegelLift c ho u' v' hu' hv' := by
  apply siegelLift_unique
  · simpa only [map_mul, map_inv, siegelLift_map] using h
  · rw [conj_pow, siegelLift_sq]
    simp

omit [CharP F 2] in
/-- The marked projective generators generate the actual scalar quotient. -/
theorem siegelGenerator_closure :
    closure {g : POmegaPlus r F | ∃ u v hu hv, g = siegelGenerator u v hu hv} = ⊤ := by
  let H := closure {g : POmegaPlus r F | ∃ u v hu hv, g = siegelGenerator u v hu hv}
  have hg (x) (hx : x ∈ elementarySubgroup (formD r F)) :
      projectiveElementaryMap (formD r F) ⟨x, hx⟩ ∈ H := by
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨u, v, hu, hv, rfl⟩ := hg
      exact subset_closure ⟨u, v, hu, hv, rfl⟩
    | one => exact H.one_mem
    | mul a b ha hb iha ihb => exact H.mul_mem iha ihb
    | inv a ha iha => exact H.inv_mem iha
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := projectiveElementaryMap_surjective (formD r F) y
  exact hg x x.property

/-- Perfectness removes any extra central factor beyond the lifted generators. -/
theorem siegelLift_closure (c : Cover E (POmegaPlus r F))
    (ho : Odd (Nat.card c.toMonoidHom.ker)) :
    closure {g : E | ∃ u v hu hv, g = siegelLift c ho u v hu hv} = ⊤ := by
  let H := closure {g : E | ∃ u v hu hv, g = siegelLift c ho u v hu hv}
  have hmap : H.map c.toMonoidHom = ⊤ := by
    apply top_unique
    rw [← siegelGenerator_closure (r := r) (F := F)]
    rw [closure_le]
    rintro g ⟨u, v, hu, hv, rfl⟩
    exact mem_map.mpr ⟨siegelLift c ho u v hu hv,
      subset_closure ⟨u, v, hu, hv, rfl⟩, siegelLift_map c ho u v hu hv⟩
  have hsurj : Function.Surjective (c.toMonoidHom.comp H.subtype) := by
    intro g
    obtain ⟨x, hx, hxg⟩ := (show g ∈ H.map c.toMonoidHom by rw [hmap]; trivial)
    exact ⟨⟨x, hx⟩, hxg⟩
  let : Group.IsPerfect E := c.isPerfect
  have hs := surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    c.toMonoidHom H.subtype hsurj c.ker_le_center
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := hs x
  exact y.property

/-- Extending the marked lifts to a homomorphism eliminates the odd kernel.
The extension premise is the global relations obligation, which the local
addition and conjugation lemmas alone do not establish. -/
theorem injective_of_siegelLift_extension (c : Cover E (POmegaPlus r F))
    (ho : Odd (Nat.card c.toMonoidHom.ker)) (s : POmegaPlus r F →* E)
    (hs : ∀ u v hu hv, s (siegelGenerator u v hu hv) = siegelLift c ho u v hu hv) :
    Function.Injective c.toMonoidHom := by
  have hfix (x : E) : s (c.toMonoidHom x) = x := by
    have hx : x ∈ closure {g : E | ∃ u v hu hv, g = siegelLift c ho u v hu hv} := by
      rw [siegelLift_closure]
      trivial
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨u, v, hu, hv, rfl⟩ := hg
      rw [siegelLift_map, hs]
    | one => simp only [map_one]
    | mul a b ha hb iha ihb => simp only [map_mul, iha, ihb]
    | inv a ha iha => simp only [map_inv, iha]
  exact Function.LeftInverse.injective hfix

end ClassicalOrthogonal.EvenCoverKernels.Plus

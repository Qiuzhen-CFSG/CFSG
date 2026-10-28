module

public import Theory.SpecificGroups.PSp4Three.Generation
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Algebra.Field.ZMod

/-!
# Ternary symplectic perfectness

Conjugacy gives a common image for nonzero-direction transvections in every
abelian quotient. That image has both order dividing three and order dividing
four, by the four-transvection identity. Generation then gives perfectness.
No large-field scalar or characteristic-two argument is used.

Adapted from Gerald Höhn, ATLAS, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
from `Atlas/LinearGroups/Symplectic/PerfectLarge.lean`, `Atlas/LinearGroups/Symplectic/AbelianImages.lean`, `Atlas/LinearGroups/Symplectic/TernaryIdentity.lean`, `Atlas/LinearGroups/Symplectic/PerfectThree.lean`.
Covered adaptations retain the ATLAS Research and Attribution License 1.0
(`LICENSES/ATLAS.txt`; citation: `LICENSES/ATLAS-CITATION.cff`).
Changes: CFSG imports and module boundaries; local namespace to avoid
collisions with other ports; unused results outside this argument omitted.
-/

@[expose] public section

noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ} {F A : Type*} [Field F] [CommGroup A]

theorem abelian_transvection_images (f : Sp n F →* A)
    {u v : Vector n F} (hu : u ≠ 0) (hv : v ≠ 0) (a : F) :
    f (transvection u a) = f (transvection v a) := by
  obtain ⟨g,_,hg⟩ := exists_generated_send hu hv
  have h := congrArg f (transvection_conjugate g u a)
  simpa [hg,map_mul,map_inv,mul_comm,mul_left_comm,mul_assoc] using h

/-- An additive parameter repeated k times is k times that parameter. -/
theorem transvection_pow (v : Vector n F) (a : F) (k : ℕ) :
    transvection v a ^ k = transvection v (k • a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,ih,← transvection_add,succ_nsmul,add_comm]

omit [CommGroup A] in
theorem perfect_of_transvections
    (h : ∀ (v : Vector n F) (a : F), transvection v a ∈ commutator (Sp n F)) :
    Group.IsPerfect (Sp n F) := by
  constructor
  apply top_unique
  rw [← transvectionGroup_eq_top (n := n) (F := F)]
  apply (Subgroup.closure_le _).mpr
  rintro t ⟨v,a,rfl⟩
  exact h v a

omit [CommGroup A] in
theorem perfect_of_abelian_images
    (h : ∀ (v : Vector n F) (a : F), Abelianization.of (transvection v a) = 1) :
    Group.IsPerfect (Sp n F) := by
  apply perfect_of_transvections
  intro v a
  rw [← Abelianization.ker_of]
  exact h v a

end Matrix.PSp4Three
end

noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F] [CharP F 3]

/-- Four orthogonal-direction transvections cancel in characteristic three. -/
theorem ternary_four_transvections (u v : Vector n F) (huv : form u v = 0) :
    transvection u 1 * transvection v 1 * transvection (u+v) 1 * transvection (u-v) 1 = 1 := by
  have hvu : form v u = 0 := by rw [form_swap,huv,neg_zero]
  apply ext_action
  intro x
  simp only [mul_smul,one_smul,transvection_apply]
  simp only [map_add,map_sub,map_smul,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,smul_eq_mul,form_self,huv,hvu,add_zero,    sub_self,mul_zero]
  funext i
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring_nf
  have hc : (3 : F) = 0 := CharP.cast_eq_zero F 3
  rw [hc,mul_zero,mul_zero,add_zero,add_zero]

end Matrix.PSp4Three
end

noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F] [CharP F 3]

/-- Uniform perfectness over the three-element field, starting at symplectic rank two. -/
theorem perfect_of_ternary_scalars (hn : 2 ≤ n)
    (hscalars : ∀ a : F, a = 0 ∨ a = 1 ∨ a = -1) : Group.IsPerfect (Sp n F) := by
  classical
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i,j] at this
  let u : Vector n F := e i
  let v : Vector n F := e j
  have hu : u ≠ 0 := by intro h; have := congrFun h (.inl i); simp [u,e] at this
  have hv : v ≠ 0 := by intro h; have := congrFun h (.inl j); simp [v,e] at this
  have hp : u+v ≠ 0 := by
    intro h; have := congrFun h (.inl i); simp [u,v,e,hij] at this
  have hm : u-v ≠ 0 := by
    intro h; have := congrFun h (.inl i); simp [u,v,e,hij] at this
  have huv : form u v = 0 := by
    change form (e i) (e j) = 0
    rw [form_e_right]
    simp [e]
  let f : Sp n F →* Abelianization (Sp n F) := Abelianization.of
  let z := f (transvection u 1)
  have hz3 : z^3=1 := by
    change f (transvection u 1)^3=1
    rw [← map_pow, transvection_pow (n := n) (F := F) u 1 3]
    have h3 : (3 : ℕ) • (1 : F) = 0 := by
      simpa only [nsmul_eq_mul,mul_one] using (CharP.cast_eq_zero F 3)
    rw [h3,transvection_zero,map_one]
  have hz4 : z^4=1 := by
    have h := congrArg f (ternary_four_transvections u v huv)
    simp only [map_mul,map_one] at h
    rw [← abelian_transvection_images f hu hv,← abelian_transvection_images f hu hp,
      ← abelian_transvection_images f hu hm] at h
    simpa only [z,pow_succ,pow_zero,one_mul] using h
  have hz : z=1 := by
    simpa only [pow_succ,hz3,one_mul] using hz4
  have hunit (w : Vector n F) (hw : w ≠ 0) : f (transvection w 1)=1 := by
    rw [← abelian_transvection_images f hu hw]
    exact hz
  apply perfect_of_abelian_images
  intro w a
  change f (transvection w a)=1
  by_cases hw : w=0
  · subst w; simp [f]
  rcases hscalars a with rfl|rfl|rfl
  · simp
  · exact hunit w hw
  · rw [← transvection_inverse,map_inv,hunit w hw,inv_one]

omit [Field F] [CharP F 3] in
/-- Perfectness for the actual three-element coefficient field. -/
theorem perfect_of_card_three (hn : 2 ≤ n) : Group.IsPerfect (Sp n (ZMod 3)) := by
  apply perfect_of_ternary_scalars (F := ZMod 3) hn
  intro a
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end Matrix.PSp4Three
end

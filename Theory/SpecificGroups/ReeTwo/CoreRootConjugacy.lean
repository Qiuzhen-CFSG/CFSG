module

public import Theory.SpecificGroups.ReeTwo.Core
public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Coordinates for the two classes of the middle Ree core root

Conjugating root 5 (index 2) changes its four noncentral tail coordinates
freely. Its last coordinate is their quadratic pairing. The inverse root
has the other value of that pairing. Thus a single binary polynomial
distinguishes the two classes. These are intrinsic core calculations;
preservation by an ambient local group is a separate assertion.

Source: the verified multiplication from Shinoda (1975), (2.3), pp.81–82,
in `Core`. The conjugator below is obtained directly from that multiplication.
-/

@[expose] public section
namespace ReeTwo.Core

/-- The quadratic coordinate distinguishing the middle root's two classes. -/
def rootOrientation (x : Core) : ZMod 2 :=
  x.b9 + x.b5 * x.b8 + x.b6 * x.b7

private def rootConjugate (a b c d e : ZMod 2) : Core :=
  ⟨0, 0, 1, 0, 0, a, b, c, d, a * d + b * c + e⟩

private theorem conjugate_root_two (x : Core) :
    x * root 2 * x⁻¹ = rootConjugate x.b0 x.b1 x.b3 x.b4 0 := by
  change mul (mul x ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩)
    (mul (mul x x) x) = _
  apply Core.ext <;> simp only [mul, rootConjugate]
  all_goals norm_num
  all_goals ring_nf
  all_goals reduce_mod_char

private theorem conjugate_root_two_inv (x : Core) :
    x * (root 2)⁻¹ * x⁻¹ = rootConjugate x.b0 x.b1 x.b3 x.b4 1 := by
  rw [← conj_inv, conjugate_root_two]
  exact (by decide +kernel : ∀ a b c d : ZMod 2,
    (rootConjugate a b c d 0)⁻¹ = rootConjugate a b c d 1) _ _ _ _

private theorem orientation_rootConjugate (a b c d e : ZMod 2) :
    rootOrientation (rootConjugate a b c d e) = e := by
  dsimp [rootOrientation, rootConjugate]
  ring_nf
  reduce_mod_char

private theorem eq_rootConjugate (x : Core)
    (h0 : x.b0 = 0) (h1 : x.b1 = 0) (h2 : x.b2 = 1)
    (h3 : x.b3 = 0) (h4 : x.b4 = 0) :
    x = rootConjugate x.b5 x.b6 x.b7 x.b8 (rootOrientation x) := by
  apply Core.ext <;> dsimp [rootConjugate]
  all_goals try first | assumption | rfl
  dsimp [rootOrientation]
  ring_nf
  reduce_mod_char

/-- Exact membership in the conjugacy class of the middle root. -/
theorem isConj_root_two_iff (x : Core) :
    IsConj (root 2) x ↔
      x.b0 = 0 ∧ x.b1 = 0 ∧ x.b2 = 1 ∧ x.b3 = 0 ∧ x.b4 = 0 ∧
        rootOrientation x = 0 := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := isConj_iff.mp h
    rw [conjugate_root_two]
    exact ⟨rfl, rfl, rfl, rfl, rfl, orientation_rootConjugate ..⟩
  · rintro ⟨h0, h1, h2, h3, h4, ho⟩
    apply isConj_iff.mpr
    refine ⟨⟨x.b5, x.b6, 0, x.b7, x.b8, 0, 0, 0, 0, 0⟩, ?_⟩
    rw [conjugate_root_two, eq_rootConjugate x h0 h1 h2 h3 h4, ho]
    rfl

/-- The inverse root has the other value of the quadratic coordinate. -/
theorem isConj_root_two_inv_iff (x : Core) :
    IsConj (root 2)⁻¹ x ↔
      x.b0 = 0 ∧ x.b1 = 0 ∧ x.b2 = 1 ∧ x.b3 = 0 ∧ x.b4 = 0 ∧
        rootOrientation x = 1 := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := isConj_iff.mp h
    rw [conjugate_root_two_inv]
    exact ⟨rfl, rfl, rfl, rfl, rfl, orientation_rootConjugate ..⟩
  · rintro ⟨h0, h1, h2, h3, h4, ho⟩
    apply isConj_iff.mpr
    refine ⟨⟨x.b5, x.b6, 0, x.b7, x.b8, 0, 0, 0, 0, 0⟩, ?_⟩
    rw [conjugate_root_two_inv, eq_rootConjugate x h0 h1 h2 h3 h4, ho]
    rfl

@[simp] theorem rootOrientation_root_two : rootOrientation (root 2) = 0 := by decide

@[simp] theorem rootOrientation_root_two_inv : rootOrientation (root 2)⁻¹ = 1 := by decide

open Subgroup
open scoped commutatorElement
private def headHom : Core →* Multiplicative (Fin 5 → ZMod 2) where
  toFun x := Multiplicative.ofAdd ![x.b0, x.b1, x.b2, x.b3, x.b4]
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> rfl
  map_mul' x y := by
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> rfl

private theorem root_two_commutes_derived (x : Core) (hx : x ∈ commutator Core) :
    root 2 * x = x * root 2 := by
  have hh := Abelianization.commutator_subset_ker headHom hx
  change headHom x = 1 at hh
  have h0 := congrArg (fun v : Multiplicative (Fin 5 → ZMod 2) => Multiplicative.toAdd v (0 : Fin 5)) hh
  have h1 := congrArg (fun v : Multiplicative (Fin 5 → ZMod 2) => Multiplicative.toAdd v (1 : Fin 5)) hh
  have h2 := congrArg (fun v : Multiplicative (Fin 5 → ZMod 2) => Multiplicative.toAdd v (2 : Fin 5)) hh
  have h3 := congrArg (fun v : Multiplicative (Fin 5 → ZMod 2) => Multiplicative.toAdd v (3 : Fin 5)) hh
  have h4 := congrArg (fun v : Multiplicative (Fin 5 → ZMod 2) => Multiplicative.toAdd v (4 : Fin 5)) hh
  change x.b0 = 0 at h0
  change x.b1 = 0 at h1
  change x.b2 = 0 at h2
  change x.b3 = 0 at h3
  change x.b4 = 0 at h4
  change mul ⟨0,0,1,0,0,0,0,0,0,0⟩ x = mul x ⟨0,0,1,0,0,0,0,0,0,0⟩
  apply Core.ext <;> simp [mul, h0, h1, h2, h3, h4]

private theorem tail_mem_derived (i : Fin 4) : root ⟨5 + i.val, by omega⟩ ∈ commutator Core := by
  have h (a b : Core) : rightComm a b ∈ commutator Core := by
    simpa [rightComm, commutatorElement_def, _root_.commutator_def] using
      (commutator_mem_commutator (show a⁻¹ ∈ (⊤ : Subgroup Core) from trivial)
        (show b⁻¹ ∈ (⊤ : Subgroup Core) from trivial))
  have h5 : rightComm (root 0) (root 2) = root 5 := by decide +kernel
  have h6 : rightComm (root 1) (root 2) = root 6 := by decide +kernel
  have h7 : rightComm (root 2) (root 3) = root 7 := by decide +kernel
  have h8 : rightComm (root 2) (root 4) = root 8 := by decide +kernel
  fin_cases i
  · exact h5 ▸ h _ _
  · exact h6 ▸ h _ _
  · exact h7 ▸ h _ _
  · exact h8 ▸ h _ _

private theorem head_of_commutes_tail (x : Core)
    (h : ∀ i : Fin 4, x * root ⟨5 + i.val, by omega⟩ = root ⟨5 + i.val, by omega⟩ * x) :
    x.b0 = 0 ∧ x.b1 = 0 ∧ x.b3 = 0 ∧ x.b4 = 0 := by
  have h5 := congrArg Core.b9 (h 0)
  have h6 := congrArg Core.b9 (h 1)
  have h7 := congrArg Core.b9 (h 2)
  have h8 := congrArg Core.b9 (h 3)
  change (mul x ⟨0,0,0,0,0,1,0,0,0,0⟩).b9 = (mul ⟨0,0,0,0,0,1,0,0,0,0⟩ x).b9 at h5
  change (mul x ⟨0,0,0,0,0,0,1,0,0,0⟩).b9 = (mul ⟨0,0,0,0,0,0,1,0,0,0⟩ x).b9 at h6
  change (mul x ⟨0,0,0,0,0,0,0,1,0,0⟩).b9 = (mul ⟨0,0,0,0,0,0,0,1,0,0⟩ x).b9 at h7
  change (mul x ⟨0,0,0,0,0,0,0,0,1,0⟩).b9 = (mul ⟨0,0,0,0,0,0,0,0,1,0⟩ x).b9 at h8
  simpa [mul] using And.intro h8 (And.intro h7 (And.intro h6 h5))

/-- Every automorphism sends the middle root into the same affine tail. -/
theorem aut_root_two_head (a : MulAut Core) :
    (a (root 2)).b0 = 0 ∧ (a (root 2)).b1 = 0 ∧ (a (root 2)).b2 = 1 ∧
    (a (root 2)).b3 = 0 ∧ (a (root 2)).b4 = 0 := by
  have hc (i : Fin 4) : a (root 2) * root ⟨5 + i.val, by omega⟩ = root ⟨5 + i.val, by omega⟩ * a (root 2) := by
    have hm := characteristic_iff_le_comap.mp
      (inferInstance : (commutator Core).Characteristic) a.symm (tail_mem_derived i)
    have hh := congrArg a (root_two_commutes_derived _ hm)
    simpa only [map_mul, MulEquiv.coe_toMonoidHom, a.apply_symm_apply] using hh
  obtain ⟨h0, h1, h3, h4⟩ := head_of_commutes_tail _ hc
  have h2 : (a (root 2)).b2 = 1 := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (a (root 2)).b2 with h2 | h2
    · have hs : a (root 2) ^ 2 = 1 := by
        rw [pow_two]
        change mul (a (root 2)) (a (root 2)) = ⟨0,0,0,0,0,0,0,0,0,0⟩
        apply Core.ext <;> simp [mul, h0, h1, h2, h3, h4]
        all_goals ring_nf
        all_goals reduce_mod_char
      have hb : (root 2) ^ 2 = 1 := a.injective (by simpa only [map_pow, map_one] using hs)
      exact False.elim ((by decide +kernel : (root 2) ^ 2 ≠ 1) hb)
    · exact h2
  exact ⟨h0, h1, h2, h3, h4⟩

/-- The polynomial is the sole obstruction to preserving the middle root class. -/
theorem isConj_root_two_aut_iff (a : MulAut Core) :
    IsConj (root 2) (a (root 2)) ↔ rootOrientation (a (root 2)) = 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := aut_root_two_head a
  simp only [isConj_root_two_iff, h0, h1, h2, h3, h4, true_and]

/-- Every automorphism preserves or interchanges the two middle-root classes. -/
theorem aut_root_two_isConj_or_inv (a : MulAut Core) :
    IsConj (root 2) (a (root 2)) ∨ IsConj (root 2)⁻¹ (a (root 2)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := aut_root_two_head a
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
      (rootOrientation (a (root 2))) with ho | ho
  · exact Or.inl ((isConj_root_two_iff _).mpr ⟨h0, h1, h2, h3, h4, ho⟩)
  · exact Or.inr ((isConj_root_two_inv_iff _).mpr ⟨h0, h1, h2, h3, h4, ho⟩)

end ReeTwo.Core


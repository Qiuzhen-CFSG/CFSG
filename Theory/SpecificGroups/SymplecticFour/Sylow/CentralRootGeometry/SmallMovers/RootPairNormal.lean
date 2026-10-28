module

public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootFamily
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Normal pairs of transvection roots

Over a characteristic-two field of order greater than two, a join of two
full transvection roots in the standard plane wing can be normal in the
whole unipotent group only when both roots are its central long root.
Conjugating a finite root by the shear produces every finite parameter.
The two-root product equations would then make every field element a root
of a quadratic with the two original parameters, a contradiction.

Source application: the root-product configuration of MS93 (5.1), printed
p.913; the literal replacement supplies the full-Sylow normalization.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private theorem root_sup_product (s t : Option F) :
    ((rootFamily s ⊔ rootFamily t : Subgroup (unipotent (F := F))) : Set _) =
      (rootFamily s : Set (unipotent (F := F))) * (rootFamily t : Set (unipotent (F := F))) := by
  let := wing_elementary (F := F) true
  apply coe_mul_of_right_le_normalizer_left
  exact (rootFamily_le_wing t).trans (((wing true).le_centralizer.trans
    (centralizer_le (rootFamily_le_wing s))).trans (Subgroup.centralizer_le_normalizer _))

omit [Finite F] in
private theorem conjugate_finite_root (s c : F) :
    element c 0 0 0 * element 0 (s^2) s 1 * (element c 0 0 0)⁻¹ =
      element 0 ((s+c)^2) (s+c) 1 := by
  rw [mul_inv_eq_iff_eq_mul,element_mul,element_mul,element_eq_iff]
  have hthree : (3:F)=1 := by
    have ht : (3:F)=2+1 := by norm_num
    rw [ht,CharTwo.two_eq_zero,zero_add]
  constructor
  · simp
  constructor
  · ring_nf
    simp [hthree,CharTwo.two_eq_zero]
  · constructor
    · simp [add_assoc,CharTwo.add_self_eq_zero]
    · simp

omit [Finite F] in
private theorem all_finite_root_elements_of_normal
    (J : Subgroup (unipotent (F := F))) [J.Normal] {s : F} (hs : finiteRoot s ≤ J) :
    ∀ x : F, element 0 (x^2) x 1 ∈ J := by
  intro x
  have hh := (inferInstance : J.Normal).conj_mem
    (element 0 (s^2) s 1) (hs ((element_mem_finiteRoot _ _ _ _ _).mpr
      ⟨rfl,by simp,by simp⟩)) (element (x-s) 0 0 0)
  rw [conjugate_finite_root,add_sub_cancel] at hh
  exact hh

private theorem not_normal_root_finite (s : F) :
    ¬ (root ⊔ finiteRoot s : Subgroup (unipotent (F := F))).Normal := by
  intro hn
  let := hn
  have hh := all_finite_root_elements_of_normal (root ⊔ finiteRoot s) le_sup_right (s+1)
  change element 0 ((s+1)^2) (s+1) 1 ∈
    ((rootFamily none ⊔ rootFamily (some s) : Subgroup (unipotent (F := F))) : Set _) at hh
  rw [root_sup_product] at hh
  obtain ⟨a,ha,b,hb,he⟩ := hh
  obtain ⟨⟨ba,ua,wa,va⟩,rfl⟩ := element_surjective a
  obtain ⟨⟨bb,ub,wb,vb⟩,rfl⟩ := element_surjective b
  dsimp at ha hb he
  obtain ⟨rfl,rfl,rfl⟩ := (element_mem_root _ _ _ _).mp ha
  obtain ⟨rfl,rfl,rfl⟩ := (element_mem_finiteRoot _ _ _ _ _).mp hb
  rw [element_mul,element_eq_iff] at he
  simp only [zero_add,zero_mul,mul_zero,add_zero] at he
  have hv := he.2.2.2
  have hw : s = s+1 := by simpa only [hv,mul_one] using he.2.2.1
  exact one_ne_zero (add_left_cancel (hw.symm.trans (add_zero s).symm))

/-- A normal join of two full transvection roots is the central long root. -/
theorem normal_root_pair_eq_central (hq : 2 < Nat.card F) (s t : Option F)
    (hn : (rootFamily s ⊔ rootFamily t).Normal) : s = none ∧ t = none := by
  cases s with
  | none =>
    cases t with
    | none => exact ⟨rfl,rfl⟩
    | some t => exact False.elim (not_normal_root_finite t hn)
  | some s =>
    cases t with
    | none =>
      have hh : (root ⊔ finiteRoot s : Subgroup (unipotent (F := F))).Normal := by
        change (finiteRoot s ⊔ root).Normal at hn
        rw [sup_comm] at hn
        exact hn
      exact False.elim (not_normal_root_finite s hh)
    | some t =>
      let := hn
      obtain ⟨x,hxs,hxt⟩ := ENat.exists_ne_ne_of_three_le (α := F)
        (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast (show 3 ≤ Nat.card F by omega)) s t
      have hh := all_finite_root_elements_of_normal (rootFamily (some s) ⊔ rootFamily (some t))
        le_sup_left x
      change element 0 (x^2) x 1 ∈
        ((rootFamily (some s) ⊔ rootFamily (some t) : Subgroup (unipotent (F := F))) : Set _) at hh
      rw [root_sup_product] at hh
      obtain ⟨a,ha,b,hb,he⟩ := hh
      obtain ⟨⟨ba,ua,wa,va⟩,rfl⟩ := element_surjective a
      obtain ⟨⟨bb,ub,wb,vb⟩,rfl⟩ := element_surjective b
      dsimp at ha hb he
      obtain ⟨rfl,rfl,rfl⟩ := (element_mem_finiteRoot _ _ _ _ _).mp ha
      obtain ⟨rfl,rfl,rfl⟩ := (element_mem_finiteRoot _ _ _ _ _).mp hb
      rw [element_mul,element_eq_iff] at he
      simp only [zero_mul,mul_zero,add_zero] at he
      have hp : (x-s)*(x-t)=0 := by
        linear_combination -he.2.1 + (s+t)*he.2.2.1 - s*t*he.2.2.2
      exact False.elim ((mul_ne_zero (sub_ne_zero.mpr hxs) (sub_ne_zero.mpr hxt)) hp)
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers

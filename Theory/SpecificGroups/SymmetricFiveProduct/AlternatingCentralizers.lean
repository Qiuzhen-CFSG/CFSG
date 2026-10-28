module
public import Theory.Alternating.Aut
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers of alternating axes in a symmetric-five product

The alternating group on five letters has trivial centralizer in its
symmetric group. Consequently the centralizer of either alternating axis
in S₅ × S₅ is the opposite full symmetric axis. The transport theorems
retain an arbitrary marking of an actual subgroup by this product.

These are the quotient-centralizer identities used in Aschbacher–Smith
10.2.1, pp.742–743.
-/

public section
open Subgroup
namespace Theory.SymmetricFiveProduct
local notation "S5" => Equiv.Perm (Fin 5)
local notation "Alt5" => alternatingGroup (Fin 5)

theorem centralizer_left_alternating_axis :
    centralizer (((Alt5).prod (⊥ : Subgroup S5)) : Set (S5 × S5)) =
      (⊥ : Subgroup S5).prod (⊤ : Subgroup S5) := by
  ext x
  constructor
  · intro hx
    have h : x.1 ∈ centralizer (Alt5 : Set S5) := by
      intro a ha
      exact congrArg Prod.fst (hx (a,1) ⟨ha,one_mem _⟩)
    rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide)] at h
    exact ⟨h,mem_top _⟩
  · rintro ⟨hx,_⟩ ⟨a,b⟩ ⟨_,hb⟩
    apply Prod.ext
    · change a * x.1 = x.1 * a
      rw [show x.1 = 1 from hx,mul_one,one_mul]
    · change b * x.2 = x.2 * b
      rw [show b = 1 from hb,one_mul,mul_one]

theorem centralizer_right_alternating_axis :
    centralizer (((⊥ : Subgroup S5).prod Alt5) : Set (S5 × S5)) =
      (⊤ : Subgroup S5).prod (⊥ : Subgroup S5) := by
  ext x
  constructor
  · intro hx
    have h : x.2 ∈ centralizer (Alt5 : Set S5) := by
      intro a ha
      exact congrArg Prod.snd (hx (1,a) ⟨one_mem _,ha⟩)
    rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide)] at h
    exact ⟨mem_top _,h⟩
  · rintro ⟨_,hx⟩ ⟨a,b⟩ ⟨ha,_⟩
    apply Prod.ext
    · change a * x.1 = x.1 * a
      rw [show a = 1 from ha,one_mul,mul_one]
    · change b * x.2 = x.2 * b
      rw [show x.2 = 1 from hx,mul_one,one_mul]

private theorem marked_centralizer {G F : Type*} [Group G] [Group F]
    (Y : Subgroup G) (e : Y ≃* F) (K : Subgroup F) :
    Y ⊓ centralizer (K.map (Y.subtype.comp e.symm.toMonoidHom) : Set G) =
      (centralizer (K : Set F)).map (Y.subtype.comp e.symm.toMonoidHom) := by
  let f := Y.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.symm.injective
  ext x
  constructor
  · rintro ⟨hxY,hxC⟩
    have he : f (e ⟨x,hxY⟩) = x := by simp only [f,MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply,coe_subtype]
    refine ⟨e ⟨x,hxY⟩,?_,he⟩
    intro k hk
    apply hf
    simpa only [map_mul,he] using hxC (f k) (mem_map_of_mem f hk)
  · rintro ⟨y,hy,rfl⟩
    refine ⟨(e.symm y).property,?_⟩
    rintro z ⟨k,hk,rfl⟩
    exact (map_mul f k y).symm.trans ((congrArg f (hy k hk)).trans (map_mul f y k))

/-- The centralizer inside the marked product of its left alternating axis. -/
theorem marked_left_alternating_centralizer {G : Type*} [Group G]
    (Y : Subgroup G) (e : Y ≃* S5 × S5) :
    Y ⊓ centralizer (((Alt5).prod (⊥ : Subgroup S5)).map
      (Y.subtype.comp e.symm.toMonoidHom) : Set G) =
      ((⊥ : Subgroup S5).prod (⊤ : Subgroup S5)).map
        (Y.subtype.comp e.symm.toMonoidHom) := by
  rw [marked_centralizer,centralizer_left_alternating_axis]

/-- The centralizer inside the marked product of its right alternating axis. -/
theorem marked_right_alternating_centralizer {G : Type*} [Group G]
    (Y : Subgroup G) (e : Y ≃* S5 × S5) :
    Y ⊓ centralizer (((⊥ : Subgroup S5).prod Alt5).map
      (Y.subtype.comp e.symm.toMonoidHom) : Set G) =
      ((⊤ : Subgroup S5).prod (⊥ : Subgroup S5)).map
        (Y.subtype.comp e.symm.toMonoidHom) := by
  rw [marked_centralizer,centralizer_right_alternating_axis]

end Theory.SymmetricFiveProduct

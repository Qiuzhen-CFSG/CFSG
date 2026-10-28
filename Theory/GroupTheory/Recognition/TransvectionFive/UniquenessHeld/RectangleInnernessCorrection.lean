module

public import Theory.GroupTheory.Hall.TwoComplementConjugacy
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
Elementary correction steps for the overlap automorphism in source 44.2.
An automorphism trivial modulo a normal two-subgroup preserves the product
with an odd solvable complement. Hall conjugacy aligns that complement by
one element of the two-subgroup. A faithful action on a pointwise fixed
subgroup then makes the aligned complement pointwise fixed as well.
-/

public section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld.RectangleInnernessCorrection
variable {G : Type*} [Group G]

/-- Pointwise fixation forces the displacement of every normalizing element
to centralize the fixed subgroup. -/
theorem displacement_mem_centralizer (E : Subgroup G) (a : MulAut G)
    (hfix : ∀ e ∈ E, a e = e) (g : G) (hg : g ∈ normalizer (E : Set G)) :
    g⁻¹ * a g ∈ centralizer (E : Set G) := by
  intro e he
  have hc : a g * e * (a g)⁻¹ = g * e * g⁻¹ := by
    have h := hfix (g * e * g⁻¹) ((mem_normalizer_iff.mp hg e).mp he)
    simpa only [map_mul, map_inv, hfix e he] using h
  calc
    e * (g⁻¹ * a g) = g⁻¹ * (g * e * g⁻¹) * a g := by group
    _ = g⁻¹ * (a g * e * (a g)⁻¹) * a g := by rw [hc]
    _ = (g⁻¹ * a g) * e := by group

/-- A subgroup preserved by an automorphism fixing its faithful action
pointwise is itself fixed pointwise. -/
theorem fixed_of_faithful_action (E X : Subgroup G) (a : MulAut G)
    (hXE : X ≤ normalizer (E : Set G))
    (hfaith : X ⊓ centralizer (E : Set G) = ⊥)
    (hX : X.map a.toMonoidHom ≤ X) (hfix : ∀ e ∈ E, a e = e) :
    ∀ x ∈ X, a x = x := by
  intro x hx
  have hd : x⁻¹ * a x ∈ X ⊓ centralizer (E : Set G) :=
    ⟨X.mul_mem (X.inv_mem hx) (hX (mem_map_of_mem _ hx)),
      displacement_mem_centralizer E a hfix x (hXE hx)⟩
  rw [hfaith, mem_bot, inv_mul_eq_one] at hd
  exact hd.symm

/-- Equality modulo a subgroup preserves its join with every subgroup. -/
theorem sup_image_eq_of_displacement (J X : Subgroup G) (a : MulAut G)
    (hmod : ∀ g : G, g⁻¹ * a g ∈ J) :
    J ⊔ X.map a.toMonoidHom = J ⊔ X := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rintro _ ⟨x,hx,rfl⟩
    change a x ∈ J ⊔ X
    have h := (J ⊔ X).mul_mem (mem_sup_right hx) (mem_sup_left (hmod x))
    simpa only [mul_inv_cancel_left] using h
  · refine sup_le le_sup_left ?_
    intro x hx
    have h := (J ⊔ X.map a.toMonoidHom).mul_mem
      (mem_sup_right (mem_map_of_mem a.toMonoidHom hx))
      (mem_sup_left (J.inv_mem (hmod x)))
    change a x * (x⁻¹ * a x)⁻¹ ∈ J ⊔ X.map a.toMonoidHom at h
    simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using h

/-- The image of an odd solvable complement can be aligned using one element
of the original normal two-subgroup. -/
theorem exists_two_correction [Finite G] (J X : Subgroup G) [J.Normal]
    [Group.IsSolvable X] (hJ : IsPGroup 2 J) (hX : Nat.Coprime 2 (Nat.card X))
    (a : MulAut G) (hmod : ∀ g : G, g⁻¹ * a g ∈ J) :
    ∃ j ∈ J, X.map (a.trans (MulAut.conj j)).toMonoidHom = X := by
  have hX' : Nat.Coprime 2 (Nat.card (X.map a.toMonoidHom)) := by
    rw [card_map_of_injective a.injective]
    exact hX
  obtain ⟨j,hj,hconj⟩ := OddHall.exists_two_conjugator_of_common_sup
    J X (X.map a.toMonoidHom) hJ hX hX'
    (by rw [normalizer_eq_top]; exact le_top)
    (by rw [normalizer_eq_top]; exact le_top)
    (sup_image_eq_of_displacement J X a hmod)
  refine ⟨j,hj,?_⟩
  have he : (a.trans (MulAut.conj j)).toMonoidHom =
      (MulAut.conj j).toMonoidHom.comp a.toMonoidHom := by ext x; rfl
  rw [he, ← map_map]
  exact hconj

/-- Aligning the odd complement preserves a pointwise fixed subgroup
centralized by the two-subgroup, and makes the complement pointwise fixed. -/
theorem exists_two_correction_fixing [Finite G] (J X E : Subgroup G) [J.Normal]
    [Group.IsSolvable X] (hJ : IsPGroup 2 J) (hX : Nat.Coprime 2 (Nat.card X))
    (hJE : J ≤ centralizer (E : Set G)) (hXE : X ≤ normalizer (E : Set G))
    (hfaith : X ⊓ centralizer (E : Set G) = ⊥)
    (a : MulAut G) (hmod : ∀ g : G, g⁻¹ * a g ∈ J)
    (hfix : ∀ e ∈ E, a e = e) :
    ∃ j ∈ J, (∀ e ∈ E, (a.trans (MulAut.conj j)) e = e) ∧
      (∀ x ∈ X, (a.trans (MulAut.conj j)) x = x) := by
  obtain ⟨j,hj,hconj⟩ := exists_two_correction J X hJ hX a hmod
  have hE : ∀ e ∈ E, (a.trans (MulAut.conj j)) e = e := by
    intro e he
    change j * a e * j⁻¹ = e
    rw [hfix e he, ← hJE hj e he, mul_inv_cancel_right]
  exact ⟨j,hj,hE,fixed_of_faithful_action E X _ hXE hfaith hconj.le hE⟩

/-- A pointwise fixed normal subgroup with trivial centralizer determines
the ambient automorphism. -/
theorem eq_one_of_fixed_normal (K : Subgroup G) [K.Normal]
    (hC : centralizer (K : Set G) = ⊥) (a : MulAut G)
    (hfix : ∀ k ∈ K, a k = k) : a = 1 := by
  ext g
  have hd := displacement_mem_centralizer K a hfix g
    (by rw [normalizer_eq_top]; trivial)
  rw [hC, mem_bot, inv_mul_eq_one] at hd
  exact hd.symm

/-- Fixing a normal join pointwise extends to the ambient group when the
common centralizer of the two factors is trivial. -/
theorem eq_one_of_fixed_normal_sup (J X E : Subgroup G) [(J ⊔ X).Normal]
    (hCJ : centralizer (J : Set G) ≤ E)
    (hEX : E ⊓ centralizer (X : Set G) = ⊥)
    (a : MulAut G) (hJ : ∀ j ∈ J, a j = j) (hX : ∀ x ∈ X, a x = x) :
    a = 1 := by
  refine eq_one_of_fixed_normal (J ⊔ X) ?_ a ?_
  · apply le_antisymm _ bot_le
    intro g hg
    have h : g ∈ E ⊓ centralizer (X : Set G) :=
      ⟨hCJ (fun j hj => hg j (mem_sup_left hj)), fun x hx => hg x (mem_sup_right hx)⟩
    rwa [hEX] at h
  · exact (show J ⊔ X ≤ a.toMonoidHom.eqLocus (MonoidHom.id G) from sup_le hJ hX)

end Theory.GroupTheory.TransvectionFive.UniquenessHeld.RectangleInnernessCorrection

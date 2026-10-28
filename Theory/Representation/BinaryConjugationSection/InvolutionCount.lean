module

public import Theory.Representation.BinaryConjugationSection
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Abel

/-!
# Counting involution lifts through free binary sections

For an involutive action on A with a binary section A/B, conjugation moves
the zero cocycle fiber bijectively to every fixed-vector fiber. Freeness
provides the required displacement preimages. Thus the number of inverted
elements in A is the fixed-space order times the number in B. If A has
exponent two, these are actual fixed lifts. The fixed-space order itself
is computed from the displacement homomorphism and its kernel.

Application and source: the 8 · 4 · 2 calculation in Aschbacher–Smith,
J.2.6, printed p.435 (PDF p.446 of `refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection

private theorem binary_neg {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (v : W) : -v = v := by
  apply neg_eq_of_add_eq_zero_left
  rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]

private theorem card_of_fibers {X Y : Type*} [Finite X] [Finite Y]
    (f : X → Y) (n : ℕ) (h : ∀ y, Nat.card {x // f x = y} = n) :
    Nat.card X = Nat.card Y * n := by
  classical
  let := Fintype.ofFinite Y
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

/-- The fixed vectors, with their literal action equation. -/
def Fixed {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : W →ₗ[ZMod 2] W) : Submodule (ZMod 2) W :=
  LinearMap.ker (f - LinearMap.id)

@[simp] theorem mem_fixed {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : W →ₗ[ZMod 2] W) (v : W) : v ∈ Fixed f ↔ f v = v := by
  simp only [Fixed, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

/-- An involutive free binary action has equally large fixed and displacement spaces. -/
theorem card_fixed_sq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : W →ₗ[ZMod 2] W) (hf : ∀ v, f (f v) = v)
    (hfree : ∀ v, f v = v → ∃ w, f w + w = v) :
    Nat.card W = Nat.card (Fixed f) * Nat.card (Fixed f) := by
  let delta : W →+ Fixed f := {
    toFun := fun w => ⟨f w + w, by simp only [mem_fixed, map_add, hf, add_comm]⟩
    map_zero' := Subtype.ext (by simp)
    map_add' := fun x y => Subtype.ext (by
      change f (x + y) + (x + y) = (f x + x) + (f y + y)
      simp only [map_add]; abel) }
  have hd : Function.Surjective delta := by
    intro v
    obtain ⟨w, hw⟩ := hfree v ((mem_fixed f v).mp v.property)
    exact ⟨w, Subtype.ext hw⟩
  have hk : delta.ker = (Fixed f).toAddSubgroup := by
    ext w
    change (delta w = 0) ↔ w ∈ Fixed f
    rw [Subtype.ext_iff, mem_fixed]
    change f w + w = 0 ↔ f w = w
    rw [add_eq_zero_iff_eq_neg, binary_neg]
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup delta.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective delta hd).toEquiv, hk]
  rfl

/-- Twisted cocycles parametrize the square-one elements in an involution coset. -/
abbrev Cocycles {A : Type*} [Group A] (s : MulAut A) := {a : A // s a = a⁻¹}

/-- Changing a lift by conjugation acts on its twisted cocycle. -/
def cocycleConj {A : Type*} [Group A] (s : MulAut A)
    (hs : ∀ a, s (s a) = a) (a : A) : Cocycles s ≃ Cocycles s where
  toFun c := ⟨a * c * (s a)⁻¹, by
    simp only [map_mul, map_inv, hs, c.property, mul_inv_rev, inv_inv]
    group⟩
  invFun c := ⟨a⁻¹ * c * (s a⁻¹)⁻¹, by
    simp only [map_mul, map_inv, hs, c.property, mul_inv_rev, inv_inv]
    group⟩
  left_inv c := by apply Subtype.ext; simp only [map_inv]; group
  right_inv c := by apply Subtype.ext; simp only [map_inv]; group

/-- Coordinates of a cocycle are fixed vectors in the binary section. -/
def cocycleMap {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (s : MulAut A) (p : A →* Multiplicative W) (f : W →ₗ[ZMod 2] W)
    (he : ∀ a, (p (s a)).toAdd = f (p a).toAdd) :
    Cocycles s → Fixed f := fun c => ⟨(p c).toAdd, by
      rw [mem_fixed, ← he, c.property, map_inv]
      exact binary_neg _⟩

private theorem cocycleMap_shift {A W : Type*} [Group A] [AddCommGroup W]
    [Module (ZMod 2) W] (s : MulAut A) (hs : ∀ a, s (s a) = a)
    (p : A →* Multiplicative W) (f : W →ₗ[ZMod 2] W)
    (he : ∀ a, (p (s a)).toAdd = f (p a).toAdd) (a : A) (c : Cocycles s) :
    (cocycleMap s p f he (cocycleConj s hs a c) : W) =
      (cocycleMap s p f he c : W) + (f (p a).toAdd + (p a).toAdd) := by
  change (p (a * c * (s a)⁻¹)).toAdd = _
  simp only [map_mul, map_inv]
  change (p a).toAdd + (p c).toAdd + -(p (s a)).toAdd = _
  rw [he, binary_neg]
  change (p a).toAdd + (p c).toAdd + f (p a).toAdd =
    (p c).toAdd + (f (p a).toAdd + (p a).toAdd)
  abel

/-- Each actual section fiber is carried to the zero fiber by conjugation. -/
theorem card_cocycles {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : MulAut A) (hs : ∀ a, s (s a) = a)
    (p : A →* Multiplicative W) (hp : Function.Surjective p)
    (f : W →ₗ[ZMod 2] W)
    (he : ∀ a, (p (s a)).toAdd = f (p a).toAdd)
    (hfree : ∀ v, f v = v → ∃ w, f w + w = v) :
    Nat.card (Cocycles s) = Nat.card (Fixed f) *
      Nat.card {c : Cocycles s // p c = 1} := by
  let F := cocycleMap s p f he
  apply card_of_fibers F
  intro v
  obtain ⟨w, hw⟩ := hfree v ((mem_fixed f v).mp v.property)
  obtain ⟨a, ha⟩ := hp (Multiplicative.ofAdd w)
  have hshift (c : Cocycles s) : (F (cocycleConj s hs a c) : W) = (F c : W) + v := by
    rw [cocycleMap_shift, ha]
    exact congrArg ((F c : W) + ·) hw
  apply Nat.card_congr
  symm
  refine Equiv.subtypeEquiv (cocycleConj s hs a) ?_
  intro c
  rw [Subtype.ext_iff, hshift]
  change p c = 1 ↔ (p c).toAdd + (v : W) = v
  rw [add_eq_right]
  rfl

variable {G : Type*} [Group G]

/-- Elements inverted by conjugation by the chosen involution. -/
abbrev Inverting (A : Subgroup G) (i : G) :=
  {a : A // i * a * i⁻¹ = (a : G)⁻¹}

private def sectionAut {H A B : Subgroup G} {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) H W}
    (d : BinaryConjugationSection H A B ρ) (i : H) : MulAut A :=
  A.normalizerMonoidHom ⟨i, d.normalized i.property⟩

private theorem sectionAut_sq {H A B : Subgroup G} {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) H W}
    (d : BinaryConjugationSection H A B ρ) (i : H) (hi : (i : G) ^ 2 = 1)
    (a : A) : sectionAut d i (sectionAut d i a) = a := by
  apply Subtype.ext
  change (i : G) * ((i : G) * a * (i : G)⁻¹) * (i : G)⁻¹ = a
  calc
    _ = (i : G) ^ 2 * a * ((i : G) ^ 2)⁻¹ := by simp only [pow_two]; group
    _ = _ := by rw [hi]; simp

/-- The actual inverted elements above a free section are counted by its fixed space. -/
theorem card_inverting_section [Finite G] {H A B : Subgroup G} {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ρ : Representation (ZMod 2) H W}
    (d : BinaryConjugationSection H A B ρ) (i : H) (hi : (i : G) ^ 2 = 1)
    (hfree : ∀ v, ρ i v = v → ∃ w, ρ i w + w = v) :
    Nat.card (Inverting A (i : G)) =
      Nat.card (Fixed (ρ i)) * Nat.card (Inverting B (i : G)) := by
  let s := sectionAut d i
  have he (a : A) : (d.coordinates (s a)).toAdd = ρ i (d.coordinates a).toAdd :=
    d.equivariant i a
  let e : Cocycles s ≃ Inverting A (i : G) :=
    Equiv.subtypeEquiv (Equiv.refl A) (fun a => by
      change (s a = a⁻¹) ↔ _
      rw [Subtype.ext_iff]
      rfl)
  let eB : {c : Cocycles s // d.coordinates c = 1} ≃ Inverting B (i : G) := {
    toFun := fun c => ⟨⟨c.val.val, (d.coordinates_eq_one_iff _).mp c.property⟩,
      congrArg Subtype.val c.val.property⟩
    invFun := fun b => ⟨⟨⟨b.val, d.kernel_le b.val.property⟩, Subtype.ext b.property⟩,
      (d.coordinates_eq_one_iff _).mpr b.val.property⟩
    left_inv := fun c => rfl
    right_inv := fun b => rfl }
  rw [← Nat.card_congr e, card_cocycles s (sectionAut_sq d i hi)
    d.coordinates d.onto (ρ i) he hfree, Nat.card_congr eB]

/-- Conjugation acts involutively on every section when the actor has square one. -/
theorem representation_sq {H : Subgroup G} {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) H W)
    (i : H) (hi : (i : G) ^ 2 = 1) (v : W) : ρ i (ρ i v) = v := by
  have hi' : i * i = 1 := by
    apply Subtype.ext
    change (i : G) * (i : G) = 1
    simpa only [pow_two] using hi
  calc
    _ = ρ (i * i) v := by rw [map_mul]; rfl
    _ = v := by rw [hi', map_one]; rfl

/-- Every fixed coordinate in a free binary section of an elementary abelian
2-group has an actual fixed lift, obtained by lifting a displacement. -/
theorem fixed_lift {H A B : Subgroup G} {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [IsElementaryAbelian 2 A]
    {ρ : Representation (ZMod 2) H W}
    (d : BinaryConjugationSection H A B ρ) (i : H) (hi : (i : G) ^ 2 = 1)
    (hfree : ∀ v, ρ i v = v → ∃ w, ρ i w + w = v)
    (v : W) (hv : ρ i v = v) :
    ∃ a : A, (d.coordinates a).toAdd = v ∧ (i : G) * a * (i : G)⁻¹ = a := by
  let s := sectionAut d i
  have hs := sectionAut_sq d i hi
  obtain ⟨w, hw⟩ := hfree v hv
  obtain ⟨a, ha⟩ := d.onto (Multiplicative.ofAdd w)
  let c : Cocycles s := cocycleConj s hs a ⟨1, by simp⟩
  refine ⟨c.val, ?_, ?_⟩
  · change (d.coordinates (a * 1 * (s a)⁻¹)).toAdd = v
    simp only [mul_one, map_mul, map_inv]
    change (d.coordinates a).toAdd +
      -(d.coordinates (s a)).toAdd = v
    have he : (d.coordinates (s a)).toAdd =
        ρ i
          (d.coordinates a).toAdd := d.equivariant i a
    rw [he, ha, binary_neg]
    exact (add_comm _ _).trans hw
  · have hc : (i : G) * c.val * (i : G)⁻¹ = (c.val : G)⁻¹ :=
      congrArg Subtype.val c.property
    rw [hc]
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (c.val : G) c.val.property

end Representation.BinaryConjugationSection

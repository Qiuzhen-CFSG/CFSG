module

public import Theory.SpecificGroups.ExoticTwoGroup.LocalModel
public import Theory.SpecificGroups.ExoticTwoGroup.CoreFusionCover
public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Data.Fintype.EquivFin

/-!
# Involution coverage in the concrete exotic core

The normal four is given by the four square words, and the special core is
characterized by its trivial outer coordinate. Its noncentral involutions have
two conjugacy classes represented by g₁ and g₁g₂. Kernel-checked certificates
show that every commuting disjoint elementary four meets both classes: choose
two distinct nonidentity elements and test their three nonidentity products.
This proves coverage without enumerating the lattice of all subgroups.

Source: Janko–Thompson, Math. Z. 113 (1970), final paragraph p.395 and
first paragraph p.396. All finite calculations are checked in Lean's kernel.
-/

namespace ExoticTwoGroup.LocalModel.CoreGeometry

/-- A computational predicate for the displayed normal four. -/
@[expose] public def inFour (x : Model) : Prop :=
  x = 1 ∨ x = a ^ 2 ∨ x = b ^ 2 ∨ x = a ^ 2 * b ^ 2

set_option synthInstance.maxSize 1024 in
public instance (x : Model) : Decidable (inFour x) := by
  unfold inFour
  infer_instance

private theorem inFour_mul : ∀ x y : Model, inFour x → inFour y → inFour (x*y) := by
  intro x y hx hy
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem inFour_inv : ∀ x : Model, inFour x → inFour x⁻¹ := by
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Membership in the square-generated four is a four-element test. -/
public theorem mem_four_iff (x : Model) : x ∈ presentation.four ↔ inFour x := by
  let W : Subgroup Model :=
    { carrier := inFour
      one_mem' := Or.inl rfl
      mul_mem' := inFour_mul _ _
      inv_mem' := inFour_inv _ }
  constructor
  · change x ∈ Subgroup.closure ({a ^ 2, b ^ 2} : Set Model) → x ∈ W
    exact fun hx => (Subgroup.closure_le W).mpr (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))) hx
  · intro hx
    have ha : a ^ 2 ∈ presentation.four := Subgroup.subset_closure (by simp [presentation])
    have hb : b ^ 2 ∈ presentation.four := Subgroup.subset_closure (by simp [presentation])
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact ha
    · exact hb
    · exact Subgroup.mul_mem _ ha hb

/-- Membership in the special core is the vanishing of the outer coordinate. -/
public theorem mem_core_iff (x : Model) : x ∈ presentation.core ↔ x.right = 1 := by
  constructor
  · let R := (SemidirectProduct.rightHom (φ := outerAction)).ker
    have h : presentation.core ≤ R := (Subgroup.closure_le R).mpr (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> rfl)
    exact fun hx => h hx
  · intro hx
    have hn : x = a ^ x.left.left.1.toAdd.val * b ^ x.left.left.2.toAdd.val *
        g₁ ^ x.left.right.1.toAdd.val * g₂ ^ x.left.right.2.toAdd.val := by
      simpa only [hx, Prod.fst_one, Prod.snd_one, toAdd_one,
        ZMod.val_zero, pow_zero, mul_one] using normal_form x
    rw [hn]
    repeat' apply Subgroup.mul_mem
    all_goals apply Subgroup.pow_mem
    all_goals exact Subgroup.subset_closure (by simp [presentation])

/- The two noncentral core classes, represented by the two actor types. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem core_classes_certificate : ∀ x : Model,
    x.right = 1 → x ^ 2 = 1 →
    inFour x ∨ (∃ c : Model, c * x * c⁻¹ = g₁) ∨
      (∃ c : Model, c * x * c⁻¹ = g₁ * g₂) := by
  decide +kernel

/-- Each involution in the core lies in the normal four or in one of two
explicit conjugacy classes. -/
public theorem core_classes (x : Model) (hx : x ∈ presentation.core)
    (hx2 : x ^ 2 = 1) :
    x ∈ presentation.four ∨ IsConj x g₁ ∨ IsConj x (g₁ * g₂) := by
  rcases core_classes_certificate x ((mem_core_iff x).mp hx) hx2 with h | h | h
  · exact Or.inl ((mem_four_iff x).mpr h)
  · exact Or.inr (Or.inl (isConj_iff.mpr h))
  · exact Or.inr (Or.inr (isConj_iff.mpr h))

@[expose] public def classOne (x : Model) : Prop :=
  x.right = 1 ∧ x.left.right.1 ≠ x.left.right.2

@[expose] public def classTwo (x : Model) : Prop :=
  x.right = 1 ∧ x.left.right.1 ≠ 1 ∧ x.left.right.2 ≠ 1

set_option synthInstance.maxSize 1024 in
public instance (x : Model) : Decidable (classOne x) := by unfold classOne; infer_instance
set_option synthInstance.maxSize 1024 in
public instance (x : Model) : Decidable (classTwo x) := by unfold classTwo; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem class_one_certificate : ∀ x : Model,
    x ^ 2 = 1 → classOne x → ∃ c : Model, c * x * c⁻¹ = g₁ := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem class_two_certificate : ∀ x : Model,
    x ^ 2 = 1 → classTwo x → ∃ c : Model, c * x * c⁻¹ = g₁ * g₂ := by
  decide +kernel

@[expose] public def eligible (x : Model) : Prop :=
  x ^ 2 = 1 ∧ ¬inFour x ∧ a ^ 2 * x = x * a ^ 2 ∧ b ^ 2 * x = x * b ^ 2

set_option synthInstance.maxSize 4096 in
public instance (x : Model) : Decidable (eligible x) := by unfold eligible; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
set_option synthInstance.maxSize 4096 in
private theorem pair_certificate : ∀ u v : {x : Model // eligible x},
    (u : Model) * v = (v : Model) * u → ¬inFour ((u : Model) * v) →
    (classOne u ∨ classOne v ∨ classOne ((u : Model) * v)) ∧
    (classTwo u ∨ classTwo v ∨ classTwo ((u : Model) * v)) := by
  decide +kernel

private theorem exists_pair_ne_one {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 4) : ∃ u v : G, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  classical
  let := Fintype.ofFinite G
  have hc : 2 < Fintype.card G := by rw [← Nat.card_eq_fintype_card, h]; decide
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hc
  by_cases ha : a = 1
  · subst a
    exact ⟨b, c, Ne.symm hab, Ne.symm hac, hbc⟩
  · by_cases hb : b = 1
    · subst b
      exact ⟨a, c, ha, Ne.symm hbc, hac⟩
    · exact ⟨a, b, ha, hb, hab⟩

private theorem four_meets_classes (V : Subgroup Model) [IsElementaryAbelian 2 V]
    (hcard : Nat.card V = 4) (hd : Disjoint presentation.four V)
    (hc : V ≤ Subgroup.centralizer (presentation.four : Set Model)) :
    (∃ y ∈ V, IsConj y g₁) ∧ (∃ y ∈ V, IsConj y (g₁ * g₂)) := by
  have ha : a ^ 2 ∈ presentation.four := (mem_four_iff _).mpr (Or.inr (Or.inl rfl))
  have hb : b ^ 2 ∈ presentation.four :=
    (mem_four_iff _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨u, v, hu, hv, huv⟩ := exists_pair_ne_one hcard
  have hu' : (u : Model) ≠ 1 := fun h => hu (Subtype.ext h)
  have hv' : (v : Model) ≠ 1 := fun h => hv (Subtype.ext h)
  have hpow (y : Model) (hy : y ∈ V) : y ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian y hy
  have hout (y : Model) (hy : y ∈ V) (hy1 : y ≠ 1) : ¬inFour y :=
    fun hh => hy1 (Subgroup.disjoint_def.mp hd ((mem_four_iff _).mpr hh) hy)
  have hel (y : Model) (hy : y ∈ V) (hy1 : y ≠ 1) : eligible y :=
    ⟨hpow y hy, hout y hy hy1, hc hy _ ha, hc hy _ hb⟩
  have huvcomm : (u : Model) * v = (v : Model) * u := by
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm u v)
  have huv1 : (u : Model) * v ≠ 1 := by
    intro h
    apply huv
    apply Subtype.ext
    calc
      (u : Model) = (u : Model) * ((v : Model) * v) := by
        rw [← pow_two, hpow v v.property, mul_one]
      _ = ((u : Model) * v) * v := (mul_assoc _ _ _).symm
      _ = v := by rw [h, one_mul]
  have huvV : (u : Model) * v ∈ V := V.mul_mem u.property v.property
  obtain ⟨h₁, h₂⟩ := pair_certificate
    ⟨u, hel u u.property hu'⟩ ⟨v, hel v v.property hv'⟩ huvcomm
    (hout _ huvV huv1)
  constructor
  · have h (y : Model) (hy : y ∈ V) (hc₁ : classOne y) : ∃ y ∈ V, IsConj y g₁ :=
      ⟨y, hy, isConj_iff.mpr (class_one_certificate y (hpow y hy) hc₁)⟩
    rcases h₁ with h₁ | h₁ | h₁
    · exact h u u.property h₁
    · exact h v v.property h₁
    · exact h _ huvV h₁
  · have h (y : Model) (hy : y ∈ V) (hc₂ : classTwo y) :
        ∃ y ∈ V, IsConj y (g₁ * g₂) :=
      ⟨y, hy, isConj_iff.mpr (class_two_certificate y (hpow y hy) hc₂)⟩
    rcases h₂ with h₂ | h₂ | h₂
    · exact h u u.property h₂
    · exact h v v.property h₂
    · exact h _ huvV h₂

/-- Every commuting elementary four disjoint from the normal four meets
both noncentral involution classes of the special core. -/
public theorem coreFusionCover : presentation.CoreFusionCover := by
  apply ExoticTwoGroup.Presentation.CoreFusionCover.of_forall
  intro V hV hcard hd hc x hx ho
  let := hV
  have hx2 : x ^ 2 = 1 := by simpa only [ho] using pow_orderOf_eq_one x
  rcases core_classes x hx hx2 with hW | h₁ | h₂
  · exact ⟨x, Or.inl hW, IsConj.refl x⟩
  · obtain ⟨⟨y, hy, hyy⟩, _⟩ := four_meets_classes V hcard hd hc
    exact ⟨y, Or.inr hy, h₁.trans hyy.symm⟩
  · obtain ⟨_, y, hy, hyy⟩ := four_meets_classes V hcard hd hc
    exact ⟨y, Or.inr hy, h₂.trans hyy.symm⟩

end ExoticTwoGroup.LocalModel.CoreGeometry

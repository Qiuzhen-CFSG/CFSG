module
public import Theory.Representation.BinaryPermutation.FiveGeometry
public import Mathlib.GroupTheory.Index

/-!
# Fixed hyperplanes for the disjoint transpositions on five letters

The two support transpositions fix distinct hyperplanes of the binary
five-point core, while their product fixes a plane. Their fixed hyperplanes
span the whole core and are exchanged by the permutation interchanging the
two supports. The pair four-group has normalizer of order eight, whose outside
elements all exchange the two transpositions. The finite checks inspect the
sixteen even-weight words and 120 permutations, never a subgroup lattice.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 5.1.7(1), printed p.633: the replacement-conjugator generation step.
-/

@[expose] public section
open Subgroup
namespace BinaryPermutation.FivePairFixedSpaces
abbrev Space := core (Fin 5)
abbrev U := Multiplicative Space
abbrev Perm := Equiv.Perm (Fin 5)
def first : Perm := Equiv.swap 0 1
def second : Perm := Equiv.swap 2 3
def exchange : Perm := Equiv.swap 0 2 * Equiv.swap 1 3

def fixedSubgroup (p : Perm) : Subgroup U where
  carrier := {x | coreRepresentation (Fin 5) p x.toAdd = x.toAdd}
  one_mem' := map_zero _
  mul_mem' {x y} hx hy := by
    change coreRepresentation (Fin 5) p (x.toAdd + y.toAdd) = x.toAdd + y.toAdd
    rw [map_add, hx, hy]
  inv_mem' {x} hx := by
    change coreRepresentation (Fin 5) p (-x.toAdd) = -x.toAdd
    rw [map_neg, hx]

@[simp] theorem mem_fixedSubgroup (p : Perm) (x : U) :
    x ∈ fixedSubgroup p ↔ coreRepresentation (Fin 5) p x.toAdd = x.toAdd := Iff.rfl

local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype Space := Subtype.fintype _
local instance (p : Perm) : DecidablePred (· ∈ fixedSubgroup p) :=
  fun x => inferInstanceAs (Decidable (coreRepresentation (Fin 5) p x.toAdd = x.toAdd))
local instance (p : Perm) : Fintype (fixedSubgroup p) := Subtype.fintype _

theorem card_fixed_first : Nat.card (fixedSubgroup first) = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
theorem card_fixed_second : Nat.card (fixedSubgroup second) = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
theorem card_fixed_product : Nat.card (fixedSubgroup (first * second)) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem decomposition : ∀ x : U,
    ∃ y z : U, y ∈ fixedSubgroup first ∧ z ∈ fixedSubgroup second ∧ y * z = x := by
  decide +kernel

theorem fixed_first_sup_fixed_second : fixedSubgroup first ⊔ fixedSubgroup second = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y,z,hy,hz,rfl⟩ := decomposition x
  exact mul_mem (mem_sup_left hy) (mem_sup_right hz)

def actionHom (p : Perm) : U →* U where
  toFun x := Multiplicative.ofAdd (coreRepresentation (Fin 5) p x.toAdd)
  map_one' := congrArg Multiplicative.ofAdd (map_zero (coreRepresentation (Fin 5) p))
  map_mul' x y := congrArg Multiplicative.ofAdd
    (map_add (coreRepresentation (Fin 5) p) x.toAdd y.toAdd)

theorem exchange_inv : exchange⁻¹ = exchange := by decide +kernel
theorem exchange_first : exchange * first * exchange⁻¹ = second := by decide +kernel
theorem exchange_second : exchange * second * exchange⁻¹ = first := by decide +kernel

theorem action_exchange_involutive (x : U) :
    actionHom exchange (actionHom exchange x) = x := by
  have h : ∀ x : U, actionHom exchange (actionHom exchange x) = x := by decide +kernel
  exact h x

theorem action_exchange_first (x : U) :
    x ∈ fixedSubgroup first ↔ actionHom exchange x ∈ fixedSubgroup second := by
  have h : ∀ x : U,
      x ∈ fixedSubgroup first ↔ actionHom exchange x ∈ fixedSubgroup second := by decide +kernel
  exact h x

theorem action_exchange_second (x : U) :
    x ∈ fixedSubgroup second ↔ actionHom exchange x ∈ fixedSubgroup first := by
  have h : ∀ x : U,
      x ∈ fixedSubgroup second ↔ actionHom exchange x ∈ fixedSubgroup first := by decide +kernel
  exact h x

theorem fixed_map_exchange_first :
    (fixedSubgroup first).map (actionHom exchange) = fixedSubgroup second := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (action_exchange_first y).mp hy
  · intro hx
    exact ⟨actionHom exchange x,(action_exchange_second x).mp hx,action_exchange_involutive x⟩

theorem fixed_map_exchange_second :
    (fixedSubgroup second).map (actionHom exchange) = fixedSubgroup first := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (action_exchange_second y).mp hy
  · intro hx
    exact ⟨actionHom exchange x,(action_exchange_first x).mp hx,action_exchange_involutive x⟩

private def pairWord : Fin 4 → Perm := ![1,first,second,first*second]
private def pairFour : Subgroup Perm where
  carrier := Set.range pairWord
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    have h : ∀ i j, ∃ k, pairWord i * pairWord j = pairWord k := by decide +kernel
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    obtain ⟨k,hk⟩ := h i j
    exact ⟨k,hk.symm⟩
  inv_mem' := by
    have h : ∀ i, (pairWord i)⁻¹ = pairWord i := by decide +kernel
    rintro _ ⟨i,rfl⟩
    exact ⟨i,(h i).symm⟩

def pairClosure : Subgroup Perm := closure ({first,second} : Set Perm)

private theorem pairClosure_eq_pairFour : pairClosure = pairFour := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨1,rfl⟩
    · have hx : x=second := hx
      subst x
      exact ⟨2,rfl⟩
  · rintro _ ⟨i,rfl⟩
    have ha : first ∈ pairClosure := subset_closure (by simp)
    have hb : second ∈ pairClosure := subset_closure (by simp)
    fin_cases i
    · exact one_mem _
    · exact ha
    · exact hb
    · exact mul_mem ha hb

theorem mem_pairClosure (p : Perm) :
    p ∈ pairClosure ↔ p=1 ∨ p=first ∨ p=second ∨ p=first*second := by
  rw [pairClosure_eq_pairFour]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [pairWord]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

theorem card_pairClosure : Nat.card pairClosure = 4 := by
  rw [pairClosure_eq_pairFour]
  have hi : Function.Injective pairWord := by decide +kernel
  change Nat.card (Set.range pairWord) = 4
  rw [←Nat.card_congr (Equiv.ofInjective _ hi)]
  simp

private def normalWord : Fin 8 → Perm :=
  ![1,first,second,first*second,exchange,first*exchange,second*exchange,first*second*exchange]
private theorem normal_inspection : ∀ p : Perm,
    (∃ i, p*first*p⁻¹ = pairWord i) → (∃ i, p*second*p⁻¹ = pairWord i) →
      ∃ j, p = normalWord j := by decide +kernel
private theorem normal_word : ∀ i j, ∃ k,
    normalWord i * pairWord j * (normalWord i)⁻¹ = pairWord k := by decide +kernel
private theorem normal_involutive : ∀ i j,
    ∃ k, (normalWord i)⁻¹ * pairWord j * normalWord i = pairWord k := by decide +kernel

private theorem normalWord_mem (i : Fin 8) :
    normalWord i ∈ normalizer (pairClosure : Set Perm) := by
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    obtain ⟨j,rfl⟩ := show x ∈ pairFour from pairClosure_eq_pairFour ▸ hx
    rw [pairClosure_eq_pairFour]
    obtain ⟨k,hk⟩ := normal_word i j
    exact ⟨k,hk.symm⟩
  · intro hx
    have hh : (normalWord i)⁻¹ * (normalWord i * x * (normalWord i)⁻¹) * normalWord i ∈ pairClosure := by
      obtain ⟨j,hj⟩ := show normalWord i * x * (normalWord i)⁻¹ ∈ pairFour from pairClosure_eq_pairFour ▸ hx
      rw [←hj,pairClosure_eq_pairFour]
      obtain ⟨k,hk⟩ := normal_involutive i j
      exact ⟨k,hk.symm⟩
    simpa [mul_assoc] using hh

private theorem normalizer_eq_range :
    (normalizer (pairClosure : Set Perm) : Set Perm) = Set.range normalWord := by
  ext p
  constructor
  · intro hp
    have ha := (mem_normalizer_iff.mp hp first).mp ((mem_pairClosure first).mpr (Or.inr (Or.inl rfl)))
    have hb := (mem_normalizer_iff.mp hp second).mp ((mem_pairClosure second).mpr (Or.inr (Or.inr (Or.inl rfl))))
    obtain ⟨i,hi⟩ := show p*first*p⁻¹ ∈ pairFour from pairClosure_eq_pairFour ▸ ha
    obtain ⟨j,hj⟩ := show p*second*p⁻¹ ∈ pairFour from pairClosure_eq_pairFour ▸ hb
    obtain ⟨k,hk⟩ := normal_inspection p ⟨i,hi.symm⟩ ⟨j,hj.symm⟩
    exact ⟨k,hk.symm⟩
  · rintro ⟨i,rfl⟩
    exact normalWord_mem i

theorem card_pairNormalizer : Nat.card (normalizer (pairClosure : Set Perm)) = 8 := by
  have hi : Function.Injective normalWord := by decide +kernel
  let e : normalizer (pairClosure : Set Perm) ≃ Set.range normalWord :=
    Equiv.setCongr normalizer_eq_range
  rw [Nat.card_congr e,←Nat.card_congr (Equiv.ofInjective _ hi)]
  simp

theorem exchange_mem_pairNormalizer : exchange ∈ normalizer (pairClosure : Set Perm) := normalWord_mem 4

theorem exchange_not_mem_pairClosure : exchange ∉ pairClosure := by
  rw [mem_pairClosure]
  decide +kernel

theorem pairNormalizer_outside_exchanges (p : Perm)
    (hp : p ∈ normalizer (pairClosure : Set Perm)) (hout : p ∉ pairClosure) :
    p * first * p⁻¹ = second ∧ p * second * p⁻¹ = first := by
  have ht : ∀ i, (∃ j, pairWord j = normalWord i) ∨
      (normalWord i * first * (normalWord i)⁻¹ = second ∧
        normalWord i * second * (normalWord i)⁻¹ = first) := by decide +kernel
  obtain ⟨i,rfl⟩ := show p ∈ Set.range normalWord from normalizer_eq_range ▸ hp
  rcases ht i with ⟨j,hj⟩ | h
  · exact (hout (pairClosure_eq_pairFour.symm ▸ (show normalWord i ∈ pairFour from ⟨j,hj⟩))).elim
  · exact h

private theorem action_inv (p : Perm) (x : U) : actionHom p⁻¹ (actionHom p x) = x := by
  change Multiplicative.ofAdd (coreRepresentation (Fin 5) p⁻¹
    (coreRepresentation (Fin 5) p x.toAdd)) = x
  rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  rfl

theorem fixed_map_conjugate (p g : Perm) :
    (fixedSubgroup g).map (actionHom p) = fixedSubgroup (p*g*p⁻¹) := by
  have hi (a : Perm) (x : Space) :
      coreRepresentation (Fin 5) a⁻¹ (coreRepresentation (Fin 5) a x) = x := by
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change coreRepresentation (Fin 5) (p*g*p⁻¹)
      (coreRepresentation (Fin 5) p y.toAdd) = coreRepresentation (Fin 5) p y.toAdd
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hi p]
    rw [(mem_fixedSubgroup g y).mp hy]
  · intro hx
    refine ⟨actionHom p⁻¹ x,?_,?_⟩
    · change coreRepresentation (Fin 5) g (coreRepresentation (Fin 5) p⁻¹ x.toAdd) =
        coreRepresentation (Fin 5) p⁻¹ x.toAdd
      have h := congrArg (coreRepresentation (Fin 5) p⁻¹) hx
      change coreRepresentation (Fin 5) p⁻¹ (coreRepresentation (Fin 5) (p*g*p⁻¹) x.toAdd) = _ at h
      simpa only [map_mul,Module.End.mul_apply,hi] using h
    · simpa only [inv_inv] using action_inv p⁻¹ x

/-- A nontrivial pair subgroup fixing an order-eight group pointwise is one
of the two support transposition groups. -/
theorem fixed_eight_subgroup_eq_transposition (A : Subgroup Perm)
    (hA : A ≤ pairClosure) (hne : A ≠ ⊥) (F : Subgroup U)
    (hcard : 8 ≤ Nat.card F) (hfix : ∀ p ∈ A, F ≤ fixedSubgroup p) :
    A = zpowers first ∨ A = zpowers second := by
  have hnprod : first*second ∉ A := by
    intro hp
    have hle := Nat.card_le_card_of_injective (inclusion (hfix _ hp))
      (inclusion_injective (hfix _ hp))
    rw [card_fixed_product] at hle
    omega
  have hcases (p : Perm) (hp : p ∈ A) : p=1 ∨ p=first ∨ p=second := by
    rcases (mem_pairClosure p).mp (hA hp) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact (hnprod (h ▸ hp)).elim
  obtain ⟨p,hp⟩ := ne_bot_iff_exists_ne_one.mp hne
  rcases hcases p p.property with h | h | h
  · exact (hp (Subtype.ext h)).elim
  · left
    have hfirst : first ∈ A := h ▸ p.property
    apply le_antisymm
    · intro x hx
      rcases hcases x hx with rfl | rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
      · exact (hnprod (A.mul_mem hfirst hx)).elim
    · exact zpowers_le.mpr hfirst
  · right
    have hsecond : second ∈ A := h ▸ p.property
    apply le_antisymm
    · intro x hx
      rcases hcases x hx with rfl | rfl | rfl
      · exact one_mem _
      · exact (hnprod (A.mul_mem hx hsecond)).elim
      · exact mem_zpowers _
    · exact zpowers_le.mpr hsecond

/-- The fixed hyperplane of either support transposition and its image under
an outside pair normalizer generate the whole core. -/
theorem fixed_sup_image_of_normalizer_outside (g p : Perm)
    (hg : g=first ∨ g=second) (hp : p ∈ normalizer (pairClosure : Set Perm))
    (hout : p ∉ pairClosure) :
    fixedSubgroup g ⊔ (fixedSubgroup g).map (actionHom p) = ⊤ := by
  obtain ⟨ha,hb⟩ := pairNormalizer_outside_exchanges p hp hout
  rw [fixed_map_conjugate]
  rcases hg with rfl | rfl
  · rw [ha]
    exact fixed_first_sup_fixed_second
  · rw [hb,sup_comm]
    exact fixed_first_sup_fixed_second

end BinaryPermutation.FivePairFixedSpaces

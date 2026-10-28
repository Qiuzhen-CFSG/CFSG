module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.EvenFive
public import Theory.Representation.BinaryPermutation.FiveAction
public import Mathlib.GroupTheory.Index
public import Theory.ElementaryAbelian.Quotient
/-!
# Mutual even actions on two deleted five-point modules

For a nontrivial elementary even actor, B.3.2 gives a strict inequality
between its order and the codimension of its fixed space. Applied in both
directions to two actual conjugation modules of order sixteen, the two
inequalities contradict each other. The conclusion retains the actual
ambient subgroups and their commutator.

Source: Aschbacher–Smith, B.3.2 and the A₅ case of 13.5.7(e).
-/

@[expose] public section
open Subgroup BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Offenders.Odd.FiveMutualActions
abbrev Core := Multiplicative (core (Fin 5))
variable {G : Type*} [Group G] {A B : Subgroup G}
/-- An actual binary five-point core in A with B's actual conjugation action. -/
structure ModuleAction (A B : Subgroup G) where
  moduleMap : Core →* G
  injective : Function.Injective moduleMap
  range_eq : moduleMap.range = A
  actor : B →* Equiv.Perm (Fin 5)
  equivariant : ∀ (b : B) (x : core (Fin 5)),
    MulAut.conj (b : G) (moduleMap (Multiplicative.ofAdd x)) =
      moduleMap (Multiplicative.ofAdd (coreRepresentation (Fin 5) (actor b) x))
namespace ModuleAction
variable (d : ModuleAction A B)
include d

theorem module_card : Nat.card A = 16 := by
  have hi : Function.Injective d.moduleMap.rangeRestrict :=
    fun x y h => d.injective (congrArg Subtype.val h)
  have hc := Nat.card_congr (Equiv.ofBijective d.moduleMap.rangeRestrict
    ⟨hi,d.moduleMap.rangeRestrict_surjective⟩)
  rw [d.range_eq] at hc
  rw [← hc]
  change Nat.card (core (Fin 5)) = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    FiveGeometry.finrank_core]
  rfl

/-- The prescribed permutation kernel is the actual centralizer. -/
theorem actor_eq_one_iff (b : B) :
    d.actor b = 1 ↔ (b : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hb
    apply mem_centralizer_iff.mpr
    intro x hx
    obtain ⟨y,rfl⟩ := d.range_eq.ge hx
    have h := d.equivariant b y.toAdd
    rw [hb] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro hb
    apply FiveGeometry.eq_one_of_fixes_hyperplane
    intro x _
    apply Multiplicative.ofAdd.injective
    apply d.injective
    rw [← d.equivariant]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp hb _ (d.range_eq.le ⟨_,rfl⟩)).symm

theorem kernel_card : Nat.card d.actor.ker = Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) := by
  have he : d.actor.ker = (B ⊓ centralizer (A : Set G) : Subgroup G).subgroupOf B := by
    ext b
    exact (d.actor_eq_one_iff b).trans (by simp only [mem_subgroupOf,mem_inf,b.property,true_and])
  rw [he]
  exact Nat.card_congr (subgroupOfEquivOfLe (show B ⊓ centralizer (A : Set G) ≤ B from inf_le_left)).toEquiv

/-- The model fixed space retains exactly the original ambient centralizer. -/
theorem fixed_card : Nat.card (fixedSpace (coreRepresentation (Fin 5)) d.actor.range) =
    Nat.card (A ⊓ centralizer (B : Set G) : Subgroup G) := by
  let F := fixedSpace (coreRepresentation (Fin 5)) d.actor.range
  let f : F → (A ⊓ centralizer (B : Set G) : Subgroup G) := fun x =>
    ⟨d.moduleMap (Multiplicative.ofAdd x.val), d.range_eq.le ⟨_,rfl⟩,
      mem_centralizer_iff.mpr (by
        intro b hb
        have he := d.equivariant ⟨b,hb⟩ x.val
        have hx := (Representation.mem_invariants _ _).mp x.property
          (⟨d.actor ⟨b,hb⟩,⟨⟨b,hb⟩,rfl⟩⟩ : d.actor.range)
        change coreRepresentation (Fin 5) (d.actor ⟨b,hb⟩) x.val = x.val at hx
        rw [hx] at he
        exact mul_inv_eq_iff_eq_mul.mp he)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      exact Subtype.ext (d.injective (congrArg Subtype.val he))
    · intro a
      obtain ⟨x,hx⟩ := d.range_eq.ge a.property.1
      have hxF : x.toAdd ∈ F := by
        apply (Representation.mem_invariants _ _).mpr
        rintro ⟨p,b,rfl⟩
        change coreRepresentation (Fin 5) (d.actor b) x.toAdd = x.toAdd
        apply Multiplicative.ofAdd.injective
        apply d.injective
        rw [← d.equivariant]
        change MulAut.conj (b : G) (d.moduleMap x) = d.moduleMap x
        rw [hx]
        exact mul_inv_eq_iff_eq_mul.mpr
          (mem_centralizer_iff.mp a.property.2 b.val b.property)
      exact ⟨⟨x.toAdd,hxF⟩,Subtype.ext hx⟩
  exact Nat.card_congr (Equiv.ofBijective f hf)

/-- Even nontrivial action gives a strict comparison with the opposite centralizer. -/
theorem strict_card [IsElementaryAbelian 2 B]
    (hne : d.actor.range ≠ ⊥) (heven : d.actor.range ≤ alternatingGroup (Fin 5)) :
    Nat.card d.actor.range * Nat.card (A ⊓ centralizer (B : Set G) : Subgroup G) < 16 := by
  have hE : IsElementaryAbelian 2 d.actor.range :=
    IsElementaryAbelian.of_surjective d.actor.rangeRestrict d.actor.rangeRestrict_surjective
  simpa only [d.fixed_card] using
    ChapterB.Offenders.Odd.even_five_card_fixed_lt d.actor.range ⟨hne,hE⟩ heven

/-- Two actual mutually acting five-point cores with even images commute.
Each hypothetical nontrivial action would give opposite strict centralizer inequalities. -/
theorem commute_of_even [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (e : ModuleAction B A) (hd : d.actor.range ≤ alternatingGroup (Fin 5))
    (he : e.actor.range ≤ alternatingGroup (Fin 5)) : ⁅A,B⁆ = ⊥ := by
  by_contra hn
  have hAB : ¬ A ≤ centralizer (B : Set G) :=
    fun h => hn (commutator_eq_bot_iff_le_centralizer.mpr h)
  have hBA : ¬ B ≤ centralizer (A : Set G) := by
    intro h
    exact hAB (le_centralizer_iff.mp h)
  have nontrivial {U W : Subgroup G} (s : ModuleAction U W)
      (h : ¬ W ≤ centralizer (U : Set G)) : s.actor.range ≠ ⊥ := by
    intro hr
    apply h
    intro w hw
    apply (s.actor_eq_one_iff ⟨w,hw⟩).mp
    exact (show s.actor ⟨w,hw⟩ ∈ (⊥ : Subgroup (Equiv.Perm (Fin 5))) from
      hr ▸ (show s.actor ⟨w,hw⟩ ∈ s.actor.range from ⟨⟨w,hw⟩,rfl⟩))
  have h₁ := d.strict_card (nontrivial d hBA) hd
  have h₂ := e.strict_card (nontrivial e hAB) he
  have hk₁ := d.actor.ker.index_mul_card
  rw [index_ker,d.kernel_card,e.module_card] at hk₁
  have hk₂ := e.actor.ker.index_mul_card
  rw [index_ker,e.kernel_card,d.module_card] at hk₂
  have hc₁ : Nat.card (A ⊓ centralizer (B : Set G) : Subgroup G) < Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) :=
    Nat.lt_of_mul_lt_mul_left (h₁.trans_eq hk₁.symm)
  have hc₂ : Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) < Nat.card (A ⊓ centralizer (B : Set G) : Subgroup G) :=
    Nat.lt_of_mul_lt_mul_left (h₂.trans_eq hk₂.symm)
  exact (lt_asymm hc₁ hc₂)
end ModuleAction
end CFSG.Quasithin.ChapterB.Offenders.Odd.FiveMutualActions

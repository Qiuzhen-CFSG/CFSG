module

public import Theory.GroupTheory.OddPrimeSectionCentralizers
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Exponent

/-!
# A symmetric-three cube cannot be a section of three-rank two

The alternating subgroups in the three coordinates form a normal
self-centralizing three-subgroup, so the target has characteristic three.
A transposition in the first coordinate centralizes the elementary nine
in the other two coordinates. The cyclic-centralizer theorem A.1.31(1)
for a surjective image of a group of three-rank at most two rules this out.

The rank bound is retained on the source of the actual surjection. There
is no assumption on the kernel and no use of rank monotonicity for an
arbitrary quotient. Only the six-element symmetric group is enumerated;
all product and section arguments are structural.
Source: Aschbacher–Smith A.1.31(1), printed pp.27–28, in the factor-count
step of 14.1.7, printed p.977.
-/

public section
open Subgroup
namespace Theory.GroupTheory
local notation "S3" => Equiv.Perm (Fin 3)
local notation "A3" => alternatingGroup (Fin 3)
local notation "D" => S3 × (S3 × S3)

private theorem a3_card : Nat.card A3 = 3 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem a3_pow (a : A3) : a ^ 3 = 1 := by
  simpa only [a3_card] using (pow_card_eq_one' (x := a))

private theorem a3_centralizer : centralizer (A3 : Set S3) ≤ A3 := by
  have ht : ∀ x : S3, (∀ a ∈ A3, a * x = x * a) → x ∈ A3 := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  exact ht

private theorem symmetricThreeCube_core :
    (A3).prod ((A3).prod A3) ≤ pCore 3 D := by
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  change (x : D) ^ 3 = 1
  apply Prod.ext
  · exact congrArg Subtype.val (a3_pow ⟨x.val.1,x.property.1⟩)
  · apply Prod.ext
    · exact congrArg Subtype.val (a3_pow ⟨x.val.2.1,x.property.2.1⟩)
    · exact congrArg Subtype.val (a3_pow ⟨x.val.2.2,x.property.2.2⟩)

private theorem symmetricThreeCube_characteristic_three :
    generalizedFitting D = pCore 3 D := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 3
  intro x hx
  apply symmetricThreeCube_core
  refine ⟨a3_centralizer ?_, a3_centralizer ?_, a3_centralizer ?_⟩
  · intro a ha
    exact congrArg Prod.fst (hx (a,1,1) (symmetricThreeCube_core ⟨ha,(A3).one_mem,(A3).one_mem⟩))
  · intro a ha
    exact congrArg (fun x : D => x.2.1)
      (hx (1,a,1) (symmetricThreeCube_core ⟨(A3).one_mem,ha,(A3).one_mem⟩))
  · intro a ha
    exact congrArg (fun x : D => x.2.2)
      (hx (1,1,a) (symmetricThreeCube_core ⟨(A3).one_mem,(A3).one_mem,ha⟩))

/-- A literal surjection onto S₃³ contradicts a three-rank bound on its source. -/
theorem not_surjective_symmetricThreeCube_of_threeRank_le_two
    {H : Type*} [Group H] [Finite H] (hrank : primeRank 3 H ≤ 2)
    (f : H →* D) (hf : Function.Surjective f) : False := by
  let t : D := (Equiv.swap 0 1,1,1)
  have ht : orderOf t = 2 := by
    apply orderOf_eq_prime
    · apply Prod.ext
      · decide +kernel
      · simp [t]
    · intro he
      have hh := congrArg Prod.fst he
      exact (by decide : (Equiv.swap (0 : Fin 3) 1) ≠ 1) hh
  let S := zpowers t
  have hS : IsPGroup 2 S := IsPGroup.of_card (n := 1) (by
    simpa only [S, Nat.card_zpowers, pow_one] using ht)
  have hSne : S ≠ ⊥ := by
    intro he
    have hm : t ∈ S := mem_zpowers t
    rw [he] at hm
    have h1 : t = 1 := hm
    simp [h1] at ht
  let C := (centralizer (S : Set D)).subgroupOf (pCore 3 D)
  let : IsCyclic C := cyclic_primeCore_centralizer_of_surjective_rank_le_two
    (by decide) hrank f hf symmetricThreeCube_characteristic_three S hS hSne
  let j : A3 × A3 →* C := {
    toFun := fun a => ⟨⟨(1,a.1,a.2),
      symmetricThreeCube_core ⟨(A3).one_mem,a.1.property,a.2.property⟩⟩, by
      change (1,(a.1 : S3),(a.2 : S3)) ∈ centralizer (S : Set D)
      change (1,(a.1 : S3),(a.2 : S3)) ∈ centralizer (zpowers t : Set D)
      rw [zpowers_eq_closure, centralizer_closure]
      apply mem_centralizer_singleton_iff.mpr
      simp [t]⟩
    map_one' := rfl
    map_mul' := fun a b => by apply Subtype.ext; apply Subtype.ext; rfl }
  have hj : Function.Injective j := by
    intro a b h
    have he := congrArg (fun x : C => (x.val.val).2) h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
  let : IsCyclic (A3 × A3) := isCyclic_of_injective j hj
  have hp : Monoid.exponent (A3 × A3) ∣ 3 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a => Prod.ext (a3_pow a.1) (a3_pow a.2))
  rw [IsCyclic.exponent_eq_card, Nat.card_prod, a3_card] at hp
  norm_num at hp

end Theory.GroupTheory

module

public import Theory.Representation.BinaryPermutation
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum

/-!
# Faithfulness and Sylow fixed vectors in the A₅ natural module

The actual binary natural module of A₅ is equivariantly isomorphic to the
augmentation core on five letters. A permutation fixing that core fixes the
whole permutation module, since the complementary constant line is fixed;
thus the natural action is faithful.

The double transpositions `(0 1)(2 3)` and `(0 2)(1 3)` generate a Sylow
four-group. Its fixed even-weight vectors are exactly `(c,c,c,c,0)`, so they
form a line of order two. The coordinate calculation is checked by kernel
reduction. Conjugating the subgroup transports its fixed vectors, and Sylow
conjugacy gives the same cardinality for every Sylow two-subgroup of A₅.

These are the concrete natural-module inputs to the A₅ branch of
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), C.1.13(c), printed pp.124–125/PDF pp.135–136,
and E.6.7, printed p.246/PDF p.257. The block and quotient identifications
are separate obligations of the source-theorem assembly.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.AlternatingLocal

open BinaryPermutation Subgroup
local notation "A5" => alternatingGroup (Fin 5)
private theorem odd_five : Odd (Fintype.card (Fin 5)) := by decide

/-- The actual binary natural representation of A₅ has trivial kernel. -/
theorem a5_natural_faithful (a : A5)
    (ha : ∀ v : natural (Fin 5), naturalRepresentation (Fin 5) a.val v = v) : a = 1 := by
  let e := coreEquivNatural (Fin 5) odd_five
  have hc (v : core (Fin 5)) : coreRepresentation (Fin 5) a.val v = v := by
    apply e.injective
    exact (coreEquivNatural_equivariant (Fin 5) odd_five a.val v).trans (ha (e v))
  have hf (v : Full (Fin 5)) : representation (Fin 5) a.val v = v := by
    let w := v - augmentation (Fin 5) v • allOne (Fin 5)
    have hw : w ∈ core (Fin 5) := by
      change augmentation (Fin 5) w = 0
      simp only [w, map_sub, map_smul, augmentation_allOne,
        odd_five.natCast_zmod_two, smul_eq_mul, mul_one, sub_self]
    have he := congrArg Subtype.val (hc ⟨w, hw⟩)
    change representation (Fin 5) a.val w = w at he
    simpa only [w, map_sub, map_smul, permute_allOne, sub_left_inj] using he
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have hi := congrFun (hf (Pi.single i 1)) (a.val i)
  simpa [Pi.single_apply] using hi.symm

private def first : A5 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def second : A5 :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def word : Fin 4 → A5 := ![1, first, second, first * second]
private def four : Subgroup A5 where
  carrier := Set.range word
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have hc : ∀ i j, ∃ k, word i * word j = word k := by decide +kernel
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hc i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have hc : ∀ i, ∃ j, (word i)⁻¹ = word j := by decide +kernel
    rintro a ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hc i
    exact ⟨j, hj.symm⟩
private theorem four_card : Nat.card four = 4 := by
  have hi : Function.Injective word := by decide +kernel
  change Nat.card (Set.range word) = 4
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  exact Nat.card_fin 4
private noncomputable def fourSylow : Sylow 2 A5 := Sylow.ofCard four (by
  rw [four_card, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]
  rw [show 60 = 2 ^ 2 * 15 by decide, Nat.factorization_mul (by decide) (by decide),
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
  rfl)

private theorem coordinate_test : ∀ v : Full (Fin 5),
    (∑ i, v i = 0 ∧ ∀ j : Fin 4, representation (Fin 5) (word j).val v = v) ↔
      v = ![v 0, v 0, v 0, v 0, 0] := by
  simp only [funext_iff, representation_apply]
  decide +kernel

private abbrev FixedCore (P : Subgroup A5) :=
  {v : core (Fin 5) // ∀ a : A5, a ∈ P → coreRepresentation (Fin 5) a.val v = v}

private theorem four_fixed_iff (v : core (Fin 5)) :
    (∀ a : A5, a ∈ four → coreRepresentation (Fin 5) a.val v = v) ↔
      v.val = ![v.val 0, v.val 0, v.val 0, v.val 0, 0] := by
  constructor
  · intro hv
    exact (coordinate_test v.val).mp ⟨v.property,
      fun j => congrArg Subtype.val (hv (word j) ⟨j, rfl⟩)⟩
  · intro hv a ha
    obtain ⟨j, rfl⟩ := ha
    exact Subtype.ext (((coordinate_test v.val).mpr hv).2 j)

private def line (c : ZMod 2) : core (Fin 5) :=
  ⟨![c, c, c, c, 0], by
    simp [mem_core, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]⟩

private def fourFixedEquiv : FixedCore four ≃ ZMod 2 where
  toFun v := v.val.val 0
  invFun c := ⟨line c, (four_fixed_iff (line c)).mpr rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((four_fixed_iff v.val).mp v.property).symm
  right_inv c := rfl

private noncomputable def fixedCoreNaturalEquiv (P : Subgroup A5) :
    FixedCore P ≃ {v : natural (Fin 5) //
      ∀ a : A5, a ∈ P → naturalRepresentation (Fin 5) a.val v = v} := by
  let e := coreEquivNatural (Fin 5) odd_five
  apply Equiv.subtypeEquiv e.toEquiv
  intro v
  constructor
  · intro hv a ha
    change naturalRepresentation (Fin 5) a.val (e v) = e v
    rw [← coreEquivNatural_equivariant]
    exact congrArg e (hv a ha)
  · intro hv a ha
    apply e.injective
    exact (coreEquivNatural_equivariant (Fin 5) odd_five a.val v).trans (hv a ha)

private noncomputable def fixedCoreConjEquiv (P : Subgroup A5) (g : A5) :
    FixedCore P ≃ FixedCore (P.map (MulAut.conj g).toMonoidHom) := by
  let ρ := coreRepresentation (Fin 5)
  let e : core (Fin 5) ≃ core (Fin 5) :=
    ⟨ρ g.val, ρ g.val⁻¹, ρ.inv_self_apply g.val, ρ.self_inv_apply g.val⟩
  apply Equiv.subtypeEquiv e
  intro v
  change (∀ a : A5, a ∈ P → ρ a.val v = v) ↔
    (∀ a : A5, a ∈ P.map (MulAut.conj g).toMonoidHom →
      ρ a.val (ρ g.val v) = ρ g.val v)
  constructor
  · intro hv a ha
    obtain ⟨b, hb, rfl⟩ := ha
    change ρ (g.val * b.val * g.val⁻¹) (ρ g.val v) = ρ g.val v
    simp only [map_mul, Module.End.mul_apply]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, hv b hb]
  · intro hv a ha
    have h := hv ((MulAut.conj g) a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    change ρ (g.val * a.val * g.val⁻¹) (ρ g.val v) = ρ g.val v at h
    have hh := congrArg (ρ g.val⁻¹) h
    simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc,
      inv_mul_cancel_left, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul,
      map_one, Module.End.one_apply] using hh

/-- A Sylow two-subgroup of the actual A₅ fixes precisely two natural vectors. -/
theorem a5_natural_sylow_fixed_card (P : Sylow 2 A5) :
    Nat.card {v : natural (Fin 5) //
      ∀ a : A5, a ∈ (P : Subgroup A5) → naturalRepresentation (Fin 5) a.val v = v} = 2 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 P fourSylow
  have he : (P : Subgroup A5).map (MulAut.conj g).toMonoidHom = four := by
    have hh := congrArg (fun Q : Sylow 2 A5 => (Q : Subgroup A5)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
    exact hh
  calc
    _ = Nat.card (FixedCore (P : Subgroup A5)) :=
      (Nat.card_congr (fixedCoreNaturalEquiv (P : Subgroup A5))).symm
    _ = Nat.card (FixedCore four) := by
      rw [← he]
      exact Nat.card_congr (fixedCoreConjEquiv (P : Subgroup A5) g)
    _ = Nat.card (ZMod 2) := Nat.card_congr fourFixedEquiv
    _ = 2 := by simp
end CFSG.Quasithin.ChapterE.Section06.AlternatingLocal

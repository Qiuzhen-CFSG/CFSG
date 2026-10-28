module

public import Theory.SpecificGroups.Rudvalis.SylowAutomorphismSolvability.FrattiniCoordinates
public import Theory.GroupTheory.PGroup.InvariantFiberAutomorphisms
public import Mathlib.Data.Fintype.List

/-!
# Intrinsic order-four fibers in the actual Rudvalis Sylow subgroup

The original binary normal forms give a bijection with the candidate.
Their coordinates are the ordered products of the proved generator images.
The five-point base detects fourth powers and squares, giving a decidable
order-four test. Thus the finite list count below is exactly the intrinsic
order-four fiber cardinality of every homomorphism with these generator
images. No numerical value of the full profile is asserted here.

Source: the original ATLAS words and normal-form convention in
Model.SylowOvergroups.RadicalCoverage.Sylow.Candidate, and the proved
five-point base in Model.FivePointBase. This is the counting interface for
the Sylow automorphism argument used by Aschbacher–Smith A.3.9.
-/

namespace Rudvalis.SylowAutomorphismSolvability.FrattiniCoordinates
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

@[expose] public def normalElement (n : Fin 16384) : Representative :=
  ⟨candidateNormalForm n, candidateNormalForm_mem n⟩

public theorem normalElement_bijective : Function.Bijective normalElement := by
  constructor
  · exact fun _ _ h => normalForm_injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨n, hn⟩ := exists_candidateNormalForm x.property
    exact ⟨n, Subtype.ext hn⟩

/-- Coordinates retain the original normal-form order, with generator zero on the left. -/
@[expose] public def normalCoordinate (n : Fin 16384) : Coordinate :=
  (List.ofFn (fun i : Fin 14 => coordinateGenerator i ^ (n.val / 2 ^ i.val % 2))).prod

public theorem coordinate_normalElement (f : Representative →* Coordinate)
    (hf : ∀ i, f (pcElement i) = coordinateGenerator i) (n : Fin 16384) :
    f (normalElement n) = normalCoordinate n := by
  have he : normalElement n =
      (List.ofFn (fun i : Fin 14 => pcElement i ^ (n.val / 2 ^ i.val % 2))).prod := by
    apply Subtype.ext
    simp only [normalElement, candidateNormalForm, Subgroup.val_list_prod, List.map_ofFn, Function.comp_def,
      Subgroup.coe_pow, pcElement]
  rw [he, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, map_pow, hf, normalCoordinate]

private theorem normal_pow_smul (n : Fin 16384) (k : ℕ) (x : Fin 4060) :
    candidateNormalForm n ^ k • x = (normalMap n)^[k] x := by
  induction k generalizing x with
  | zero => exact one_smul Model x
  | succ k ih =>
    rw [pow_succ', mul_smul, ih, normal_smul, Function.iterate_succ_apply']

public theorem normalElement_pow_eq_one_iff (n : Fin 16384) (k : ℕ) :
    normalElement n ^ k = 1 ↔
      ∀ i : Fin 5, (normalMap n)^[k] (i.castLE (by decide)) = i.castLE (by decide) := by
  constructor
  · intro h i
    have he := congrArg (fun g : Representative => (g : Model) • (i.castLE (by decide) : Fin 4060)) h
    simpa only [Subgroup.coe_pow, normalElement, normal_pow_smul, OneMemClass.coe_one,
      one_smul] using he
  · intro h
    apply Subtype.ext
    apply Rudvalis.eq_of_smul_first_five
    intro i
    simpa only [Subgroup.coe_pow, normalElement, normal_pow_smul, OneMemClass.coe_one,
      one_smul] using h i

/-- A decidable test on the five-point base, equivalent to order exactly four. -/
@[expose] public def orderFourTest (n : Fin 16384) : Bool :=
  decide (∀ i : Fin 5, (normalMap n)^[4] (i.castLE (by decide)) = i.castLE (by decide)) &&
  !decide (∀ i : Fin 5, (normalMap n)^[2] (i.castLE (by decide)) = i.castLE (by decide))

public theorem orderFourTest_iff (n : Fin 16384) :
    orderFourTest n = true ↔ orderOf (normalElement n) = 4 := by
  simp only [orderFourTest, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, ← normalElement_pow_eq_one_iff]
  constructor
  · rintro ⟨h4, h2⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
  · intro h
    constructor
    · simpa only [h] using pow_orderOf_eq_one (normalElement n)
    · intro h2
      have hd := orderOf_dvd_of_pow_eq_one h2
      rw [h] at hd
      norm_num at hd

/-- The finite computation uses the literal normal-form bijection and coordinates. -/
@[expose] public def profileCount (v : Coordinate) : ℕ :=
  ((List.finRange 16384).filter (fun n => decide (normalCoordinate n = v) && orderFourTest n)).length

public theorem predicateFiberCard_eq_profileCount (f : Representative →* Coordinate)
    (hf : ∀ i, f (pcElement i) = coordinateGenerator i) (v : Coordinate) :
    f.predicateFiberCard (fun x => orderOf x = 4) v = profileCount v := by
  classical
  let e : Fin 16384 ≃ Representative := Equiv.ofBijective normalElement normalElement_bijective
  have he : Nat.card {x : Representative // f x = v ∧ orderOf x = 4} =
      Nat.card {n : Fin 16384 // normalCoordinate n = v ∧ orderFourTest n = true} := by
    apply Nat.card_congr
    exact (e.subtypeEquiv (fun n => by
      simp only [e, Equiv.ofBijective_apply, coordinate_normalElement f hf, orderFourTest_iff])).symm
  change Nat.card {x : Representative // f x = v ∧ orderOf x = 4} = _
  rw [he, Nat.card_eq_fintype_card]
  let l := (List.finRange 16384).filter (fun n => decide (normalCoordinate n = v) && orderFourTest n)
  have hm (n : Fin 16384) : n ∈ l.toFinset ↔ normalCoordinate n = v ∧ orderFourTest n = true := by
    simp [l]
  rw [Fintype.card_of_subtype l.toFinset hm]
  exact List.toFinset_card_of_nodup ((List.nodup_finRange 16384).filter _)

/-- An actual Frattini quotient map together with the literal finite
counting formula needed by the intrinsic automorphism-profile argument. -/
public theorem exists_frattini_coordinate_with_profile :
    ∃ f : Representative →* Coordinate, Function.Surjective f ∧
      f.ker = frattini Representative ∧
      (∀ i, f (pcElement i) = coordinateGenerator i) ∧
      ∀ v, f.predicateFiberCard (fun x => orderOf x = 4) v = profileCount v := by
  obtain ⟨f, hs, hk, hf⟩ := exists_frattini_coordinate
  exact ⟨f, hs, hk, hf, predicateFiberCard_eq_profileCount f hf⟩

end Rudvalis.SylowAutomorphismSolvability.FrattiniCoordinates

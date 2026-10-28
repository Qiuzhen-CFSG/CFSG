module
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Data.ZMod.Basic
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero

/-!
# A proper Sylow overgroup of three-rank two in S₅ wreath C₂

The product action on the 25 functions C₂ → Fin 5 has a fixed point under
every two-subgroup. Its stabilizer is proper and contains the product of
the two four-point stabilizers. Each factor has three-rank at least one,
so their faithful product has three-rank at least two.

This is the model rank input needed in the minimal-parabolic application
of Aschbacher--Smith E.2.2 and 15.2.4, printed pp.215--216,1106.
-/

public section
open Subgroup MulAction Theory.GroupTheory
namespace Theory.SpecificGroups.SymmetricFive.WreathRank
local notation "C2" => Multiplicative (ZMod 2)
local notation "W" => RegularWreathProduct (Equiv.Perm (Fin 5)) C2
local notation "Points" => C2 → Fin 5
private def swap : C2 := Multiplicative.ofAdd 1
private theorem swap_ne_one : swap ≠ 1 := by decide
private theorem index_cases (i : C2) : i = 1 ∨ i = swap := by
  revert i
  decide

private instance : MulAction W Points where
  smul w v i := w.left i (v (w.right⁻¹ * i))
  one_smul v := by
    funext i
    change (1 : Equiv.Perm (Fin 5)) (v ((1 : C2)⁻¹ * i)) = v i
    simp
  mul_smul a b v := by
    funext i
    change (a.left i * b.left (a.right⁻¹ * i)) (v ((a.right * b.right)⁻¹ * i)) =
      a.left i (b.left (a.right⁻¹ * i) (v (b.right⁻¹ * (a.right⁻¹ * i))))
    simp [mul_assoc]

private theorem point_stabilizer_rank (i : Fin 5) :
    1 ≤ primeRank 3 (stabilizer (Equiv.Perm (Fin 5)) i) := by
  have hi : (stabilizer (Equiv.Perm (Fin 5)) i).index = 5 := by
    rw [index_stabilizer, orbit_eq_univ]
    simp
  have hc := (stabilizer (Equiv.Perm (Fin 5)) i).card_mul_index
  have hSym : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  rw [hi,hSym] at hc
  have hcard : Nat.card (stabilizer (Equiv.Perm (Fin 5)) i) = 24 := by omega
  by_contra h
  have hz : primeRank 3 (stabilizer (Equiv.Perm (Fin 5)) i) = 0 := by omega
  have hn := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
  rw [hcard] at hn
  exact hn (by decide)

private theorem pair_stabilizer_rank (v : Points) :
    2 ≤ primeRank 3 (stabilizer W v) := by
  let A := stabilizer (Equiv.Perm (Fin 5)) (v 1)
  let B := stabilizer (Equiv.Perm (Fin 5)) (v swap)
  let j : A × B →* W := {
    toFun := fun p => ⟨fun i => if i = 1 then p.1.val else p.2.val,1⟩
    map_one' := by
      apply RegularWreathProduct.ext
      · funext i
        simp
      · rfl
    map_mul' := by
      intro p q
      apply RegularWreathProduct.ext
      · funext i
        by_cases hi : i = 1 <;> simp [hi,RegularWreathProduct.mul_left]
      · rfl }
  have hj : Function.Injective j := by
    intro p q h
    have h₁ := congrArg (fun w : W => w.left 1) h
    have h₂ := congrArg (fun w : W => w.left swap) h
    apply Prod.ext
    · exact Subtype.ext (by simpa [j] using h₁)
    · exact Subtype.ext (by simpa [j,swap_ne_one] using h₂)
  have hmem (p : A × B) : j p ∈ stabilizer W v := by
    change (j p) • v = v
    funext i
    change (if i = 1 then p.1.val else p.2.val) (v ((1 : C2)⁻¹ * i)) = v i
    rcases index_cases i with rfl | rfl
    · simp only [inv_one,one_mul]
      exact p.1.property
    · simp only [inv_one,one_mul,if_neg swap_ne_one]
      exact p.2.property
  have hmon := Theory.GroupTheory.primeRank_le_of_injective 3 (j.codRestrict _ hmem)
    (fun p q h => hj (congrArg Subtype.val h))
  have hA := point_stabilizer_rank (v 1)
  have hB := point_stabilizer_rank (v swap)
  rw [primeRank_prod_eq_add] at hmon
  change 1 ≤ primeRank 3 A at hA
  change 1 ≤ primeRank 3 B at hB
  omega

private theorem pair_stabilizer_ne_top (v : Points) : stabilizer W v ≠ ⊤ := by
  intro htop
  obtain ⟨x,hx⟩ := exists_ne (v 1)
  let w : W := ⟨fun _ => Equiv.swap (v 1) x,1⟩
  have hw : w ∈ stabilizer W v := htop ▸ mem_top _
  change (fun i => w.left i (v (w.right⁻¹ * i))) = v at hw
  have he := congrFun hw 1
  exact hx (by simpa only [w,inv_one,one_mul,Equiv.swap_apply_left] using he)

/-- Every Sylow two-subgroup has a proper overgroup of three-rank at least two. -/
theorem exists_proper_sylow_overgroup_rank_two (P : Sylow 2 W) :
    ∃ B : Subgroup W, (P : Subgroup W) ≤ B ∧ B ≠ ⊤ ∧ 2 ≤ primeRank 3 B := by
  obtain ⟨v,hv⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card Points (by
    norm_num [Nat.card_fun])
  exact ⟨stabilizer W v,(fun g hg => hv ⟨g,hg⟩),pair_stabilizer_ne_top v,
    pair_stabilizer_rank v⟩
end Theory.SpecificGroups.SymmetricFive.WreathRank

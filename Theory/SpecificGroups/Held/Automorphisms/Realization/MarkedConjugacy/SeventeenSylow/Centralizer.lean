module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.Data
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Separation
public import Mathlib.GroupTheory.Sylow

/-!
# A small centralizer for the Held element of order seventeen

A graph automorphism commuting with `c = a*b` and fixing vertex zero fixes
its entire c-orbit and the unique fixed point of c. Adjacency to these
anchors successively fixes vertices 1, 3, and 2. The previously certified
four-point stabilizer is trivial. Evaluation at zero therefore injects the
centralizer into its cycle-signature cell, whose checked size is 255.

If seventeen divided the cyclic subgroup's index, a subgroup of order
17² would contain it. Groups of prime-square order are abelian, so this
subgroup would lie in the centralizer, contradicting the bound 255 < 289.

Source: the literal ATLAS HeG1-p2058B0 action and graph in `GraphData`.
The finite checks are in `SeventeenSylow/Data.lean`; graph preservation is
an explicit premise here, discharged separately by `Preservation.lean`.
-/

namespace Held.Realization.MarkedConjugacy.Seventeen
open Held.NormalizerGraph Held.NormalizerGraph.CardBound

private theorem fixes_zero_eq_one (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ preservingGroup)
    (hcomm : ∀ x, σ (c x) = c (σ x)) (h0 : σ 0 = 0) : σ = 1 := by
  have hf : σ 293 = 293 := (c_fixed_iff _).mp (by
    rw [← hcomm, (c_fixed_iff 293).mpr rfl])
  have hp (n : ℕ) : σ ((c ^ n) 0) = (c ^ n) 0 := by
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      simpa only [pow_succ', Equiv.Perm.mul_apply] using (hcomm ((c ^ n) 0)).trans
        (congrArg c ih)
  have ha : ∀ x ∈ anchors, σ x = x := by
    rw [anchors_eq]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hx
      exact hp n
    · have he := List.mem_singleton.mp hx
      subst x
      exact hf
  have h1 := unique_one (σ 1) (baseSignature_invariant anchors σ hσ ha 1)
  have h3 := unique_three (σ 3) (baseSignature_invariant anchors σ hσ ha 3)
  have ha' : ∀ x ∈ anchors ++ [1, 3], σ x = x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ha x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact h1
      · exact h3
  have h2 := unique_two (σ 2) (baseSignature_invariant _ σ hσ ha' 2)
  apply four_fixed_eq_one σ hσ
  intro x hx
  have he : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
  rcases he with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private theorem code_invariant (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ preservingGroup)
    (hcomm : ∀ x, σ (c x) = c (σ x)) (n : ℕ) (x y : Fin 2058) :
    code n (σ x) (σ y) = code n x y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp only [code, ← hcomm, ih, hσ x y]

private theorem cycleCode_invariant (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ preservingGroup)
    (hcomm : ∀ x, σ (c x) = c (σ x)) (x : Fin 2058) :
    cycleCode (σ x) = cycleCode x := by
  unfold cycleCode
  rw [← hcomm]
  exact code_invariant σ hσ hcomm 4 x (c x)

public abbrev centralizer : Subgroup He := Subgroup.centralizer ({a * b} : Set He)

public theorem centralizer_card_le (hgraph : permutationGroup ≤ preservingGroup) :
    Nat.card centralizer ≤ 255 := by
  have hc (g : centralizer) (x : Fin 2058) :
      representation g.val (c x) = c (representation g.val x) := by
    have h := congrArg representation (Subgroup.mem_centralizer_singleton_iff.mp g.property)
    exact congrArg (fun σ : Equiv.Perm (Fin 2058) => σ x) h
  have hi : Function.Injective (fun g : centralizer => representation g.val 0) := by
    intro g h he
    dsimp only at he
    have h0 : representation (h⁻¹ * g).val 0 = 0 := by
      change ((representation h.val)⁻¹ * representation g.val) 0 = 0
      change (representation h.val).symm (representation g.val 0) = 0
      rw [he, Equiv.symm_apply_apply]
    have hone := fixes_zero_eq_one (representation (h⁻¹ * g).val)
      (hgraph (h⁻¹ * g).val.property) (hc (h⁻¹ * g)) h0
    have heq : h⁻¹ * g = 1 := by
      apply Subtype.ext
      apply representation_injective
      exact hone
    exact (inv_mul_eq_one.mp heq).symm
  let f : centralizer → {x : Fin 2058 // cycleCode x = cycleCode 0} :=
    fun g => ⟨representation g.val 0, cycleCode_invariant _ (hgraph g.val.property) (hc g) 0⟩
  have hf : Function.Injective f := fun g h he => hi (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective f hf).trans cycleCode_card.le

public theorem cyclic_index_not_dvd_of_centralizer_bound
    (hbound : Nat.card centralizer ≤ 255) :
    ¬ 17 ∣ (Subgroup.zpowers (a * b)).index := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  intro hd
  have hcard : Nat.card (Subgroup.zpowers (a * b)) = 17 ^ 1 := by
    rw [Nat.card_zpowers, orderOf_ab, pow_one]
  have hd' : 17 ^ (1 + 1) ∣ Nat.card He := by
    rw [← (Subgroup.zpowers (a * b)).card_mul_index, hcard]
    simpa only [pow_succ, pow_zero, one_mul] using Nat.mul_dvd_mul_left 17 hd
  obtain ⟨K, hK, hle⟩ := Sylow.exists_subgroup_card_pow_succ hd' hcard
  have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hK).is_comm.comm
  have hab : a * b ∈ K := hle (Subgroup.mem_zpowers (a * b))
  have hKC : K ≤ centralizer := by
    intro k hk
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg (fun z : K => z.val) (hcomm (⟨k, hk⟩ : K) (⟨a * b, hab⟩ : K))
  have hh := Nat.card_le_card_of_injective (Subgroup.inclusion hKC)
    (Subgroup.inclusion_injective hKC)
  rw [hK] at hh
  omega

end Held.Realization.MarkedConjugacy.Seventeen

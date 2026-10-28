module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Counting
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations
public import Theory.SpecificGroups.ReeF4.AutomorphismTwoRank

/-!
# The Ree elementary two-subgroup bound: source assembly

Sylow conjugacy transports an arbitrary elementary subgroup of the literal
Ree carrier to the actual positive fixed subgroup, preserving its order.
The first half of GLS3 Lemma 3.3.9 replaces it by an elementary subgroup in D
of at least the same order. The checked counting argument then applies the
square, order and commutator calculations in `RootCalculationFacts`.

The two concrete root branches discharge the premises of the retained
conditional assembly. Thus `card_le` proves the bound for every elementary
two-subgroup of the literal model when m >= 1. Its exact Chapter B application
is in `HigherRecognition/EvenTwisted/ReeF4/ElementaryTwoBound.lean`.
The Tits endpoint is separate.

Source: GLS3, Lemma 3.3.9, printed pp.134–135,
`refs/KGroup/GLS3/chapter3.tex`; Guralnick–Malle, *Classification of 2F-modules,
II*, Table 13 (internal p.53) and Lemma 8.8 (pp.57–58).
-/

public section
noncomputable section
namespace ReeF4.ElementaryTwoBound
open Subgroup Parabolics

/-- Sylow conjugacy puts an elementary subgroup in the actual positive subgroup
without changing its order. -/
theorem exists_elementary_le_unipotent (m : ℕ) (B : Subgroup (Model m))
    (hB : IsElementaryAbelian 2 B) :
    ∃ E : Subgroup (Model m), E ≤ unipotent m ∧ IsElementaryAbelian 2 E ∧
      Nat.card E = Nat.card B := by
  let := hB
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hBQ⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  let P := sylowOfOddIndex m (AutomorphismTwoRank.unipotent_index_odd m)
  let e := Q.equiv P
  let f : Q →* Model m := (P : Subgroup (Model m)).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let B' := B.subgroupOf (Q : Subgroup (Model m))
  let : IsElementaryAbelian 2 B' := IsElementaryAbelian.subgroupOf hBQ
  refine ⟨B'.map f, ?_, IsElementaryAbelian.map f, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    rw [← sylowOfOddIndex_coe m (AutomorphismTwoRank.unipotent_index_odd m)]
    exact (e y).property
  · rw [Subgroup.card_map_of_injective hf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv

/-- GLS3 Lemma 3.3.9 assembled from its two independent root-calculation branches.
This conditional interface is retained for separate applications of the branches. -/
theorem card_le_of_root_calculations {m : ℕ} (_hm : 1 ≤ m)
    (hreplace : ∀ E : Subgroup (Model m), E ≤ unipotent m →
      IsElementaryAbelian 2 E → ∃ F : Subgroup (Model m),
        F ≤ D m ∧ IsElementaryAbelian 2 F ∧ Nat.card E ≤ Nat.card F)
    (hroot : RootCalculationFacts m)
    (B : Subgroup (Model m)) (hB : IsElementaryAbelian 2 B) :
    Nat.card B ≤ 2 ^ (5 * (2 * m + 1)) := by
  obtain ⟨E, hEU, hE, hcard⟩ := exists_elementary_le_unipotent m B hB
  obtain ⟨F, hFD, hF, hEF⟩ := hreplace E hEU hE
  rw [← hcard]
  exact hEF.trans (card_le_in_D_of_root_calculations m hroot F hFD hF)

/-- The upper bound in GLS3 Lemma 3.3.9 on the literal Ree model in the simple
range. Here the coefficient-field order is 2^(2m+1), denoted q² in GLS. -/
theorem card_le (m : ℕ) (hm : 1 ≤ m)
    (B : Subgroup (Model m)) (hB : IsElementaryAbelian 2 B) :
    Nat.card B ≤ 2 ^ (5 * (2 * m + 1)) :=
  card_le_of_root_calculations hm (Replacement.exists_elementary_le_D m hm)
    (rootCalculationFacts m hm) B hB

end ReeF4.ElementaryTwoBound

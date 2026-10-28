module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.LiteralLocal.Action

/-!
# Generation by the two literal Held locals

The involution a*w*a*w⁻¹*a, with w the second max3 generator, normalizes the
literal seed: each conjugated seed generator is a checked word in the same
twelve generators. Together with the two generators of the published max5
conjugate it contains explicit words for Held.a and Held.b. The certified
four-point base checks the identities in the original degree-2058 carrier.

The retained discovery script uses GAP only to find the words; all identities
and subgroup containments below are checked by Lean. No maximality, simplicity,
ambient order or intrinsic seed identification is assumed.
Source: GLS3 Table 5.3p; Aschbacher--Smith, printed p.526; ATLAS max3 and max5.
-/

public section
namespace Held.AutomorphismLocalPair.LiteralLocal
open Subgroup TwoLocalCandidates TwoLocalCandidates.MaximalNormalizerCatalogue

/-- A short element of the actual seed normalizer. -/
@[expose] def extra : He :=
  a * LocalPairs.PairCoverage.localWord false * a *
    (LocalPairs.PairCoverage.localWord false)⁻¹ * a

attribute [local irreducible] extra

private def conjugateWord : Fin 12 → List (Fin 12)
  | 0 => [4, 0, 5]
  | 1 => [2, 1, 3]
  | 2 => [3, 1, 4]
  | 3 => [2, 1, 4]
  | 4 => [2, 3, 4]
  | 5 => [2, 3, 5]
  | 6 => [10, 3]
  | 7 => [10, 5]
  | 8 => [2, 3, 6]
  | 9 => [6]
  | 10 => [1, 7, 1]
  | 11 => [2, 3, 5]

set_option maxRecDepth 16384 in
private theorem conjugate_check : ∀ i : Fin 12, ∀ v : Fin 4,
    (representation extra * seedPerm i * (representation extra)⁻¹) ⟨v.val, by omega⟩ =
      seedPermWord (conjugateWord i) ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem conjugate_eq (i : Fin 12) :
    extra * seedGen i * extra⁻¹ = seedWord (conjugateWord i) := by
  apply eq_of_four_point_images
  simp only [map_mul, map_inv, ← seedPerm_eq, ← seedPermWord_eq]
  exact conjugate_check i

/-- Membership is proved against the actual twelve seed generators. -/
theorem extra_mem_normalizer : extra ∈ representativeLargeLocal := by
  have hle : representativeLargeSeed ≤
      representativeLargeSeed.comap (MulAut.conj extra).toMonoidHom := by
    apply seed_le_of_generators
    intro i
    change extra * seedGen i * extra⁻¹ ∈ representativeLargeSeed
    rw [conjugate_eq]
    exact seedWord_mem _
  have hm : representativeLargeSeed.map (MulAut.conj extra).toMonoidHom ≤
      representativeLargeSeed := (map_le_iff_le_comap).mpr hle
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact eq_of_le_of_card_ge hm (by
    rw [card_map_of_injective (MulAut.conj extra).injective])

private def pairGen : Fin 3 → He
  | 0 => (MulAut.conj (conjugator 0)) max5First
  | 1 => (MulAut.conj (conjugator 0)) max5Second
  | 2 => extra

private def pairWord (w : List ℤ) : He :=
  (w.map (fun k => if k < 0 then (pairGen (Fin.ofNat 3 (k.natAbs - 1)))⁻¹
    else pairGen (Fin.ofNat 3 (k.natAbs - 1)))).prod

private def wordA : List ℤ := [-3, 1, -2, -1, -1, 3, 1, 1, 2, -1, -2, -3, 2, -3, -2, -1, -1, -1, -1, 3, 2]
private def wordB : List ℤ := [-3, 2, -1, -2, -1, -2, -3, -2, -1, -1, 3, -1, 3, -2, 3, 2, 3, 3, -1, -2, 3, 2, 1, 3, -2, -1, -1, -3, -3, -3, -1, -1, -2, -1, -2, -3, 1, -3, -1, 2, -1, -1, 2, 1, 2, -1, -1, -1, -3, -1, -1, -1, -1, -3, -2, -2, -1, -2, -1, 3, -2, -1, -2, 3]

set_option maxRecDepth 16384 in
private theorem wordA_eq : pairWord wordA = a := by
  apply eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
private theorem wordB_eq : pairWord wordB = b := by
  apply eq_of_four_point_images
  decide +kernel

private theorem pairGen_mem (i : Fin 3) :
    pairGen i ∈ centerLocal LocalPairs.SylowGeometry.Calculations.representative ⊔
      representativeLargeLocal := by
  fin_cases i
  · apply (show centerLocal LocalPairs.SylowGeometry.Calculations.representative ≤
      centerLocal LocalPairs.SylowGeometry.Calculations.representative ⊔
        representativeLargeLocal from le_sup_left)
    rw [representative_centerLocal]
    exact mem_map_of_mem _ max5First_mem
  · apply (show centerLocal LocalPairs.SylowGeometry.Calculations.representative ≤
      centerLocal LocalPairs.SylowGeometry.Calculations.representative ⊔
        representativeLargeLocal from le_sup_left)
    rw [representative_centerLocal]
    exact mem_map_of_mem _ max5Second_mem
  · exact (show representativeLargeLocal ≤
      centerLocal LocalPairs.SylowGeometry.Calculations.representative ⊔
        representativeLargeLocal from le_sup_right) extra_mem_normalizer

private theorem pairWord_mem (w : List ℤ) :
    pairWord w ∈ centerLocal LocalPairs.SylowGeometry.Calculations.representative ⊔
      representativeLargeLocal := by
  apply list_prod_mem
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact inv_mem (pairGen_mem _)
  · exact pairGen_mem _

/-- The literal pair generates Held because it contains both original generators. -/
theorem locals_generate :
    centerLocal LocalPairs.SylowGeometry.Calculations.representative ⊔
      representativeLargeLocal = ⊤ := by
  apply top_unique
  rw [← closure_pair]
  apply (closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · rw [← wordA_eq]
    exact pairWord_mem wordA
  · have hx : x = b := Set.mem_singleton_iff.mp hx
    rw [hx, ← wordB_eq]
    exact pairWord_mem wordB

end Held.AutomorphismLocalPair.LiteralLocal

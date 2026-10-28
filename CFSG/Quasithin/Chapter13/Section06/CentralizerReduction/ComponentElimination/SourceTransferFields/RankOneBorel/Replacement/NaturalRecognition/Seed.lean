module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.Contracts

/-!
# The invariant, noncentral source seed span

The literal ⟨z^K⟩ is a subrepresentation of W_K. Membership in Y_z and
Tᵥ-invariance of K force this subrepresentation to have nonzero commutator.
These facts use no block or natural-module witness. They locate the module
constituent to which the exact 13.6.15 exclusion applies.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.14–15,
pp.929–930 (PDF pp.946–947).
-/

@[expose] public section


open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
open ComponentSelection
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]
local notation "W" => WK K L T z v
local notation "ρ" => componentRepresentation K L T z v hL hz

omit [IsElementaryAbelian 2 (WK K L T z v)] in
theorem seedSpan_le_WK : conjugateSpanBy (zpowers z) K ≤ W :=
  conjugateSpanBy_mono le_rfl ((le_conjugateSpanBy K (Tv T v)).trans le_sup_left)

theorem seedSpace_invariant (a : plusImage K L T z v hL hz K)
    (w : Additive W) (hw : w ∈ seedSpace K L T z v) :
    ρ a w ∈ seedSpace K L T z v := by
  obtain ⟨k, rfl⟩ := componentMap_surjective K L T z v hL hz a
  change w.toMul.val ∈ conjugateSpanBy (zpowers z) K at hw
  change (ρ (componentMap K L T z v hL hz k) w).toMul.val ∈ conjugateSpanBy (zpowers z) K
  change (k : G) * w.toMul.val * (k : G)⁻¹ ∈ conjugateSpanBy (zpowers z) K
  exact (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy (zpowers z) K k.property)
    w.toMul.val).mp hw

noncomputable def seedSubrepresentation : Subrepresentation ρ where
  toSubmodule := seedSpace K L T z v
  apply_mem_toSubmodule := seedSpace_invariant K L T z v hL hz

theorem seedSpace_not_le_invariants (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    ¬ seedSpace K L T z v ≤ (ρ).invariants := by
  intro hfixed
  let w : W := ⟨z, le_conjugateSpanBy _ _ (mem_zpowers z)⟩
  have hw : Additive.ofMul w ∈ seedSpace K L T z v := le_conjugateSpanBy _ _ (mem_zpowers z)
  have hc := (invariants_iff K L T z v hL hz w).mp (hfixed hw)
  have hfix : K ≤ centralizer ({z} : Set G) := by
    intro k hk
    apply mem_centralizer_iff.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact (mem_centralizer_iff.mp hc k hk).symm
  exact (invariant_component_consequences K L T z v hK hn).1.2
    ((starPreimage_starImage_centralizes_seed_iff z v K hK.1.1).mpr hfix)

theorem seedSpace_commutator_ne_bot (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    subspaceCommutator ρ (seedSpace K L T z v) ⊤ ≠ ⊥ := by
  intro he
  have hh := (subspaceCommutator_eq_bot_iff ρ (seedSpace K L T z v) ⊤).mp he
  apply seedSpace_not_le_invariants K L T z v hL hz hK hn
  intro w hw a
  exact hh hw ⟨a, mem_top a⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition

end

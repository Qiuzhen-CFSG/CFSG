module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingCentralFactorSource
/-!
# The original alternating-five Sylow bound

The marked source Sylow is the order-128 dihedral wreath group times the
literal block centralizer, whose order is at most two. Its order is thus
at most 256, as required by the full-Sylow component exclusion.

Source: Aschbacher–Smith 2.4.29, printed p.545.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem MinimalBlockSetup.single_alternating_sylow_card_le_256
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    Nat.card ((d.S : Subgroup d.H).map d.H.subtype) ≤ 256 := by
  let Di := centralizer (d.block : Set d.H)
  obtain ⟨eS,_⟩ := d.single_alternating_marked_sylow_model hG T hM hTM hu hST hsingle hA
  have hcD : Nat.card Di ≤ 2 := by
    have hh := d.single_alternating_centralizer_card_le_two hG T hM hTM hu hST hsingle hA
    rw [←d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA,
      card_map_of_injective d.H.subtype_injective] at hh
    exact hh
  have hcS : Nat.card d.S = 128 * Nat.card Di := by
    rw [Nat.card_congr eS.toEquiv, Nat.card_prod, SymmetricFourWreath.card_P]
  rw [card_map_of_injective d.H.subtype_injective, hcS]
  omega
end CFSG.Quasithin.Chapter2

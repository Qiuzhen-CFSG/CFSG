module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.OriginalGeometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.NormalizerAction

/-!
# The original fixed-plane normalizer and its prime-to-three bound

The earlier local data and the fixed-line centralizer bound construct the
fusion inputs of 15.3.46. Its final clause places the normalizer of the actual
fixed plane in M. Compatible coordinates then apply 15.3.49(5), retaining only
the prime-to-three order of the original module centralizer in M.

Source: Aschbacher–Smith, 15.3.46(5) and 15.3.49(5), printed pp.1141–1143.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.NormalizerPrime
open TerminalSourceEndgame.OriginalSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc P E : Subgroup G}

theorem fixedPlane_normalizer_le
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (hfixed : centralizer (fixedPlane P (planeStabilizer T P) : Set G) ≤ M) :
    normalizer (fixedPlane (localModule T M) (planeStabilizer T P) : Set G) ≤ M := by
  let := standard_elementary earlier.natural
  have hdef := definite_of_standard earlier.natural earlier.plane_le
    earlier.plane_card earlier.plane_definite
  have h46 := FusionCore.lemma_15_3_46_of_earlier_inputs
    (quadraticAction earlier.natural)
    (GoldschmidtCore.earlierFusionInputs_of_fixed_centralizer earlier hfixed) hdef
  exact h46.2.2.2.2.1

theorem fixedPlane_normalizer_three_prime
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (hfixed : centralizer (fixedPlane P (planeStabilizer T P) : Set G) ≤ M)
    (hc : Nat.Coprime 3
      (Nat.card (M ⊓ centralizer (localModule T M : Set G) : Subgroup G))) :
    Nat.Coprime 3 (Nat.card
      (normalizer (fixedPlane (localModule T M) (planeStabilizer T P) : Set G))) := by
  let := standard_elementary earlier.natural
  obtain ⟨k⟩ := coordinates_from_standard earlier.natural
    (definite_of_standard earlier.natural earlier.plane_le earlier.plane_card
      earlier.plane_definite)
  obtain ⟨i, hi⟩ := k.plane_eq
  have hN := fixedPlane_normalizer_le earlier hfixed
  rw [hi] at hN ⊢
  exact (FusionCore.CosetSetup.ExtraspecialLocal.NormalizerAction.lemma_15_3_49_5_of_centralizer_three_prime T earlier.ordering.1.2 k.action i hN hc).2

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.NormalizerPrime

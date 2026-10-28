module
public import Theory.AtlasPort.LinearGroups.G2.SevenSylowOvergroupTransport
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Theory.GroupTheory.TwoPrimeSolvable
public import Theory.GroupTheory.SolvableSylowOvergroups

/-!
# Solvable proper Sylow overgroups in G₂(2)′

The checked seven-divisibility theorem makes every proper overgroup of a
full Sylow two-subgroup have order prime to seven. Its remaining prime
divisors are two and three, so Burnside's two-prime theorem gives solvability.
This excludes the small derived G₂ endpoint in the containing FF-action
analysis of Aschbacher--Smith 10.2.9, printed p.751. The full group G₂(2)
and its actual commutator subgroup remain distinct.

The imported split-octonion model and word calculations retain the ATLAS
attribution and license; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.BinaryDerived

/-- Every proper overgroup of a full Sylow two-subgroup in G₂(2)′ is solvable. -/
theorem solvableSylowOvergroups :
    SolvableSylowOvergroups (commutator (Atlas.G2.Model (ZMod 2))) := by
  intro S H hSH hH
  apply isSolvable_of_prime_dvd_card_eq_two_or_prime H Nat.prime_three
  intro p hp hd
  have h7 : ¬ 7 ∣ Nat.card H := fun h => hH
    (BinaryParabolicPair.SevenSylowOvergroups.eq_top_of_sylow_of_seven_dvd S H hSH h)
  have hcard : Nat.card H ∣ 6048 := by
    have h := H.card_subgroup_dvd_card
    rw [LieAutomorphismExtensions.card_binaryDerived] at h
    exact h
  have hc : p ∣ 2^5 * 3^3 * 7 := hd.trans hcard
  rcases hp.dvd_mul.mp hc with h23 | hseven
  · rcases hp.dvd_mul.mp h23 with htwo | hthree
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow htwo))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow hthree))
  · have he : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hseven
    exact (h7 (he ▸ hd)).elim

end Atlas.G2.BinaryDerived

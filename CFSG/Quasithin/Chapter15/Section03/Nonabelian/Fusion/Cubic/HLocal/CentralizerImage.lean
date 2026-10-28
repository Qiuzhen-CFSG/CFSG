module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.Geometry
public import Theory.GroupAction.PrimeGroupFixedImage

/-!
# The image of the cubic centralizer through the extraspecial kernel

Orbit counting on the two-power quotient fibers proves that C_H(D_H)
maps onto the entire actor centralizer. This is an actual image equality,
valid without a split extension. Counting its kernel and image then computes
its Sylow two-groups and preserves their embedding into the original G.

Source: Aschbacher–Smith 15.3.60, printed p.1150.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
variable {G : Type*} [Group G]

/-- The cubic centralizer covers its actual actor centralizer. -/
lemma actor_centralizer_image [Finite G] (Z : Subgroup G)
    (P : Sylow 3 (centralizerH Z)) :
    (centralizer ((P : Subgroup (centralizerH Z)) : Set (centralizerH Z))).map
      (QuotientGroup.mk' (pCore 2 (centralizerH Z))) =
      centralizer (((P : Subgroup (centralizerH Z)).map
        (QuotientGroup.mk' (pCore 2 (centralizerH Z)))) : Set (ActorQuotient Z)) := by
  apply centralizer_map_of_prime_free_kernel _ (QuotientGroup.mk'_surjective _) ?_ _ P.isPGroup'
  rw [QuotientGroup.ker_mk']
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := centralizerH Z)).exists_card_eq
  rw [hn]
  exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal

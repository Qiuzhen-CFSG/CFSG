module

public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Sylow normalizers through a central quotient

A surjection maps a Sylow normalizer onto the normalizer of the image Sylow.
If its kernel is central, that kernel already lies in the original normalizer,
so taking the inverse image recovers exactly that normalizer. In particular,
the Borel defined in a central quotient lifts to the actual Sylow normalizer.

This is the elementary quotient comparison used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, E.6.8, printed pp.247–248.
No assumption on the order of the center is needed.
-/

public section

open Subgroup
namespace Sylow

variable {G H : Type*} [Group G] [Group H] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A central-kernel surjection preserves Sylow normalizers by inverse image. -/
theorem normalizer_comap_of_central_kernel (S : Sylow p G) (f : G →* H)
    (hf : Function.Surjective f) (hk : f.ker ≤ center G) :
    (normalizer (S.mapSurjective hf : Set H)).comap f = normalizer (S : Set G) := by
  change (normalizer ((S : Subgroup G).map f : Set H)).comap f = _
  rw [← S.normalizer_map_surjective f hf]
  exact comap_map_eq_self (hk.trans (center_le_normalizer _))

/-- The normalizer of the image Sylow in G/Z(G) has precisely N_G(S) as
its full preimage, including when Z(G) has odd-order elements. -/
theorem normalizer_comap_quotient_center (S : Sylow p G) :
    (normalizer (S.mapSurjective (QuotientGroup.mk'_surjective (center G)) :
      Set (G ⧸ center G))).comap (QuotientGroup.mk' (center G)) =
      normalizer (S : Set G) :=
  S.normalizer_comap_of_central_kernel _ (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])

end Sylow

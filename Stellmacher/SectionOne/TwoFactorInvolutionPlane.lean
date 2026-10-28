module

public import Stellmacher.SectionOne.TwoFactorCanonicalCoordinates

/-!
# The canonical rank-two involution plane

Under the canonical two-factor hypotheses of Stellmacher (1.7), an order-two
subgroup supplementing the Baumann subgroup in the Sylow subgroup exchanges
the two natural four-element supports. The coordinate extraction proves this
for the supplied action. The diagonal displacement calculation then gives an
order-four commutator plane, its order-two Baumann-fixed line, a nontrivial
Sylow-fixed vector, and transitivity of the actual actor centralizer on the
nonidentity plane vectors.

No invariance of the entire plane under the Sylow subgroup is asserted.
The centralizer is in the acting group, as in the barred centralizer of
Stellmacher (9.3), printed p50/PDF40 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionOne

universe u

/-- The canonical two-factor swapping involution has a transitive commutator plane. -/
public theorem oneSeven_two_factor_involution_plane
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (S : Sylow 2 K)
    (hgen : oneE (V := V) (S : Subgroup K) ⊔ (S : Subgroup K) = ⊤)
    (hunique : IsUniqueMaximalContaining (S : Subgroup K) ⊤)
    (hfixed : FixedPoints.subgroup (oneE (V := V) (S : Subgroup K)) V = ⊥)
    (hcount : (oneSevenFactors (G := K) (V := V)).card = 2)
    (Y : Subgroup K) (hYS : Y ≤ (S : Subgroup K)) (hYcard : Nat.card Y = 2)
    (hSY : (S : Subgroup K) = oneB (V := V) (S : Subgroup K) ⊔ Y) :
    let W := commutatorAction Y V
    Nat.card W = 4 ∧
      Nat.card (W ⊓ FixedPoints.subgroup (oneB (V := V) (S : Subgroup K)) V :
        Subgroup V) = 2 ∧
      (W ⊓ FixedPoints.subgroup (S : Subgroup K) V ≠ ⊥) ∧
      (∀ vector ∈ W, vector ≠ 1 → ∀ target ∈ W, target ≠ 1 →
        ∃ actor ∈ Subgroup.centralizer (Y : Set K), actor • vector = target) := by
  obtain ⟨coordinates⟩ := oneSeven_two_factor_action_coordinates
    h S hgen hunique hfixed hcount Y hYS hYcard hSY
  exact swappedFactorActionCoordinates_involution_plane (S : Subgroup K)
    (oneB (V := V) (S : Subgroup K)) Y hSY hYcard coordinates

end Stellmacher.SectionOne

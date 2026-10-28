module

public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.HexadBound.NativeAction

/-!
# Assembly of the relative hexad kernel bound

Quotient a central two-extension by the derived subgroup of the full hexad
radical. This preserves the native A₆ lift and yields an abelian radical.
The original derived kernel has cardinality at most the product of the two
layer bounds. Thus the pairing calculation and the abelian module calculation
together give the precise `HexadLiftBound` consumed by `TwoPrimary`.

Both calculations remain explicit hypotheses here. In particular this
conditional assembly does not assert the unconditional M₂₂ multiplier bound.
Source: Aschbacher–Smith I.1.3(4), printed p.407, with I.2.2(6), printed p.412.
-/

public section
namespace Sporadic.Mathieu.M22UniversalMultiplier
open Subgroup
open HexadBound
universe u

/-- The nonabelian pairing layer and the abelian module layer give exactly
the relative bound required by the global central-transfer argument. -/
theorem hexadLiftBound_of_layer_bounds
    (hpair : RadicalDerivedBound.{u}) (hab : AbelianRadicalBound.{u}) :
    HexadLiftBound.{u} := by
  intro D _ _ q hq hc hp hs
  let N := radicalDerived q
  let π := QuotientGroup.mk' N
  let qN := abelianProjection q
  have hqN : Function.Surjective qN := abelianProjection_surjective q hq
  have hcN : qN.ker ≤ center (D ⧸ N) :=
    CentralDerivedKernel.quotient_ker_le_center q hc N (radicalDerived_le_ker q)
  have hpN : IsPGroup 2 qN.ker := by
    change IsPGroup 2 (QuotientGroup.lift N q (radicalDerived_le_ker q)).ker
    rw [QuotientGroup.ker_lift]
    exact hp.map π
  have hsN : ∃ s : alternatingGroup (Fin 6) →* D ⧸ N,
      qN.comp s = m22HexadSection m22Hexad123_mem := by
    obtain ⟨s, hs⟩ := hs
    refine ⟨π.comp s, ?_⟩
    ext a : 1
    exact DFunLike.congr_fun hs a
  have hN := hpair D q hq hc hp hs
  have hquot := hab (D ⧸ N) qN hqN hcN hpN hsN
    (abelianProjection_radical_commutative q)
  exact (CentralDerivedKernel.card_le_quotient q N (radicalDerived_le_ker q)).trans
    (by change Nat.card N * Nat.card (qN.ker ⊓ _root_.commutator (D ⧸ N) :
          Subgroup (D ⧸ N)) ≤ 4
        exact (Nat.mul_le_mul hN hquot).trans (by decide))

end Sporadic.Mathieu.M22UniversalMultiplier

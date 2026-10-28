module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicNormalization.SmallInvariant.Lifting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicNormalization.SmallInvariant.Overgroups
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicNormalization.SmallInvariant.Natural

/-!
# Lifting small-subgroup invariance to the full parabolic

Let G map onto SL₃(2) with two-group kernel and a marked natural subgroup Z.
If a kernel subgroup K has order at most four, [K,O²(G)] lies in Z, and K
is normalized by the kernel and O²(P), then a nonzero P-fixed vector on Z
forces P to normalize K.

First O²(P) fixes K ∩ Z by the natural-module calculation. Commutator
idempotence then makes it centralize K. The O²(G)-orbit of each k ∈ K has
at most eight elements; its centralizer image contains the model residual
and consequently the whole parabolic. Lifting a centralizer element leaves
only a kernel element, which already normalizes K.

All natural coordinates, the arbitrary marking, relative subgroup structure,
and the two distinct residual conventions are preserved. Source: MS93,
*Pushing up weak BN-pairs of rank two* (1993), printed p.883 immediately
before the first (1.7)(i) application; pp.847–848 and residual notation p.832.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicNormalization
open Subgroup
open scoped commutatorElement
open RankOnePairing

private theorem sl_two_perfect : IsPPerfect 2 SL := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  intro N hN hp
  rcases hN.eq_bot_or_eq_top with h | h
  · subst N
    have hSL : IsPGroup 2 SL := hp.of_equiv QuotientGroup.quotientBot
    obtain ⟨n, hn⟩ := hSL.exists_card_eq
    rw [Matrix.PSL3Two.card_SL] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; decide
    have hh := (show Nat.Prime 3 by decide).dvd_of_dvd_pow h3
    norm_num at hh
  · exact h

/-- Small subgroups fixed modulo a marked natural Z upgrade invariance under
O²(P) to invariance under the full parabolic P. -/
theorem small_fixed_preimage_parabolic_normalized
    {G : Type*} [Group G] [Finite G]
    (π : G →* SL) (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (flag : SL) (side : Bool) (Z K : Subgroup G) [Z.Normal]
    (_hZQ : Z ≤ π.ker) (n : NaturalFactor π ⊤ Z ⊥)
    (hfixed : Z ⊓ centralizer (parabolic π flag side : Set G) ≠ ⊥)
    (hKQ : K ≤ π.ker) (hcard : Nat.card K ≤ 4)
    (hcomm : ⁅K, pResidual 2 G⁆ ≤ Z)
    (hQN : π.ker ≤ normalizer (K : Set G))
    (hTN : (pResidual 2 (parabolic π flag side)).map (parabolic π flag side).subtype ≤
      normalizer (K : Set G)) :
    parabolic π flag side ≤ normalizer (K : Set G) := by
  let P := parabolic π flag side
  let T := (pResidual 2 P).map P.subtype
  have hJ : K ⊓ Z ≤ centralizer (P : Set G) :=
    SmallInvariant.Natural.small_intersection_centralizes hπ n flag side K hfixed hcard hTN
  have hTK : T ≤ centralizer (K : Set G) :=
    SmallInvariant.Lifting.centralizes_of_intersection_centralizes P K Z
      (hker.to_le hKQ) hTN hcomm hJ
  have hL : (pResidual 2 G).map π = ⊤ := by
    rw [map_pResidual_of_surjective 2 π hπ, (pResidual_eq_top_iff 2 SL).mpr sl_two_perfect]
  have hZ : Nat.card Z ≤ 8 := by
    rw [Nat.card_congr n.equivOfBot.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  have hP : P.map π = modelParabolic flag side := map_comap_eq_self_of_surjective hπ _
  have hT : T.map π = Matrix.PSL3Two.MarkedAutomorphisms.residual
      (modelParabolic flag side) := by
    rw [map_embedded_pResidual, hP]
    rfl
  apply SmallInvariant.Lifting.normalized_of_small_centralizer_overgroups
    π P K (pResidual 2 G) Z T 8 hL (map_pResidual_le 2 P.subtype)
    hQN hcomm hZ hTK
  intro A hA hi
  rw [hP]
  apply SmallInvariant.Overgroups.small_index_overgroup flag side A _ hi
  rwa [hT] at hA


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicNormalization

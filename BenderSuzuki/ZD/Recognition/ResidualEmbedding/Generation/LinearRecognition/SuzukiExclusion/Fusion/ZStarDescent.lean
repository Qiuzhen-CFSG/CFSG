module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.ZStarDescent.Lift
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.ZStarDescent.Normalizer

/-!
# The final Suzuki Z-star descent and invariant Sylow lift

The literal quotient construction, Z-star supplement, inversion and abelianness
of the odd core, quotient Sylow subgroup and torus-invariant lift are assembled
here. The normalizer calculation proves that the actual image of Q = N_M(AU)
has trivial odd core and order prime to p. Thus its intersection with the odd
core of M/A is trivial, and the latter is inverted by the image of U and is
abelian. Its p-core is Sylow; coprime torus action on the full preimage then
gives a torus-invariant Sylow subgroup of M.

The final theorem retains only the earlier Sylow geometry, order-two and weak
closure conclusions as explicit intermediate inputs. Their producers and the
contradiction with Lemma 14.4(a) remain with the parent Fusion assembly. Torus
semiregularity and the centralizer embedding are not needed again after these
intermediates have been supplied. All quotients use A normal relative to M;
`pPrimeCore 2` denotes O₂′, not O² or O²′.

Source: GLS, Volume 4, Chapter 2, conclusion of Proposition 14.1,
`refs/KGroup/GLS4/Chapter2.tex`, lines 2620–2630.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion.ZStarDescent
open Subgroup

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The quotient descent and invariant lift with the two local normalizer
conclusions explicit. The final theorem below discharges both premises. -/
public theorem exists_torus_invariant_sylow_of_normalizer
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) (hU : Nat.card g.U = 2) (hweak : QuotientFusion d g)
    (p : ℕ) [Fact p.Prime]
    (hpD : ¬ p ∣ Nat.card (residualPairStabilizer M t)) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    let Qbar := (normalizerAU g).map (QuotientGroup.mk' A)
    pPrimeCore 2 Qbar = ⊥ → ¬ p ∣ Nat.card Qbar →
      ∃ R : Sylow p M,
        residualCommutator M t ≤ normalizer ((R : Subgroup M).map M.subtype : Set G) := by
  dsimp only
  intro hcore hpQ
  exact exists_torus_invariant_sylow_of_quotient_pCore_sylow d g p hpD
    (quotient_pCore_sylow_of_normalizer d g s hU hweak p hcore hpQ)

/-- The image of Q meets the odd core of M/A trivially. -/
public theorem oddCore_disjoint_normalizerAU_image
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) (hU : Nat.card g.U = 2) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    Disjoint (pPrimeCore 2 (M ⧸ A)) ((normalizerAU g).map (QuotientGroup.mk' A)) := by
  exact oddCore_disjoint_of_normalizer_oddCore_eq_bot d g
    (normalizerAU_image_oddCore_eq_bot d g s hU)

/-- Every nonidentity element of the image of U inverts the odd core of M/A. -/
public theorem oddCore_inverted
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) (hU : Nat.card g.U = 2) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    let pi := QuotientGroup.mk' A
    ∀ u ∈ (g.U.subgroupOf M).map pi, u ≠ 1 →
      ∀ x ∈ pPrimeCore 2 (M ⧸ A), u * x * u⁻¹ = x⁻¹ := by
  exact oddCore_inverted_of_disjoint d g hU
    (oddCore_disjoint_normalizerAU_image d g s hU)

/-- The odd core of the literal quotient M/A is abelian. -/
public theorem oddCore_abelian
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) (hU : Nat.card g.U = 2) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    IsMulCommutative (pPrimeCore 2 (M ⧸ A)) := by
  exact oddCore_abelian_of_normalizer_oddCore_eq_bot d g hU
    (normalizerAU_image_oddCore_eq_bot d g s hU)

/-- The concluding descent in Proposition 14.1: a prime above the field
exponent and absent from D admits a torus-invariant Sylow subgroup of M.
In particular this applies to the primitive prime in Lemma 14.4(a), without
any additional premise about the normalizer or the quotient odd core. -/
public theorem exists_torus_invariant_sylow
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) (hU : Nat.card g.U = 2) (hweak : QuotientFusion d g)
    (p : ℕ) [Fact p.Prime] (hp_gt : 2 * m + 1 < p)
    (hpD : ¬ p ∣ Nat.card (residualPairStabilizer M t)) :
    ∃ R : Sylow p M,
      residualCommutator M t ≤ normalizer ((R : Subgroup M).map M.subtype : Set G) := by
  have hp2 : p ≠ 2 := by have := d.parameter_pos; omega
  exact exists_torus_invariant_sylow_of_normalizer d g s hU hweak p hpD
    (normalizerAU_image_oddCore_eq_bot d g s hU)
    (prime_not_dvd_normalizerAU_image d g s hU p hp2 hpD)

end BenderSuzuki.ZD.SuzukiExclusion.ZStarDescent

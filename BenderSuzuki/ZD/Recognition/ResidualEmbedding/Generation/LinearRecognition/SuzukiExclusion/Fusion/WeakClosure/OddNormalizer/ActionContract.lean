module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.Centralizers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Interfaces

/-!
# The literal odd-normalizer action interface

The actor is N_M(S)/S, with S and K carried through the actual inclusions
and quotient map. The vector group is the image of S in M/M°.
`ActionData` specifies conjugation, faithfulness and the torus centralizer
facts used in the Fitting argument. No inhabitant is asserted, and it
contains no invariance or Frobenius conclusion.

Construction of this action and the Fitting argument can proceed independently;
the OddNormalizer assembly must supply the action before using the latter.
Source: GLS4, Chapter 2, Lemma 14.9, `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- M/M°, with normality relative to the actual point stabilizer. -/
@[expose] public def pointQuotient (d : Context Z M z t m) :=
  letI : ((closure (Z ∩ (M : Set G))).subgroupOf M).Normal :=
    distinguishedClosure_normal d.minimal.disconnected
  M ⧸ (closure (Z ∩ (M : Set G))).subgroupOf M

public instance pointQuotientGroup (d : Context Z M z t m) : Group (pointQuotient d) := by
  letI : ((closure (Z ∩ (M : Set G))).subgroupOf M).Normal :=
    distinguishedClosure_normal d.minimal.disconnected
  exact QuotientGroup.Quotient.group _

public instance pointQuotientFinite (d : Context Z M z t m) : Finite (pointQuotient d) := by
  unfold pointQuotient
  infer_instance

/-- The source projection M → M/M°. -/
@[expose] public def pointProjection (d : Context Z M z t m) : M →* pointQuotient d :=
  letI : ((closure (Z ∩ (M : Set G))).subgroupOf M).Normal :=
    distinguishedClosure_normal d.minimal.disconnected
  QuotientGroup.mk' _

/-- S-bar in the actual point-stabilizer quotient. -/
@[expose] public def sylowImage (d : Context Z M z t m) (g : LocalGeometry Z M z t m) :
    Subgroup (pointQuotient d) := (g.S.subgroupOf M).map (pointProjection d)

/-- The normalizer of S, computed inside M. -/
public abbrev normalizerInM (g : LocalGeometry Z M z t m) : Subgroup M :=
  normalizer (g.S.subgroupOf M : Set M)

/-- The literal source actor N_M(S)/S. -/
public abbrev quotient (g : LocalGeometry Z M z t m) :=
  normalizerInM g ⧸ (g.S.subgroupOf M).subgroupOf (normalizerInM g)

/-- The projection of the source normalizer onto its quotient by S. -/
@[expose] public def projection (g : LocalGeometry Z M z t m) :
    normalizerInM g →* quotient g := QuotientGroup.mk' _

/-- K-tilde, using the actual two inclusions followed by N_M(S) → N_M(S)/S. -/
@[expose] public def torusImage (g : LocalGeometry Z M z t m) : Subgroup (quotient g) :=
  (((residualCommutator M t).subgroupOf M).subgroupOf (normalizerInM g)).map (projection g)

/-- The order divisibility used in the exceptional arithmetic branch. -/
public theorem quotient_card_dvd (g : LocalGeometry Z M z t m) :
    Nat.card (quotient g) ∣ Nat.card M :=
  (card_dvd_of_surjective (projection g) (QuotientGroup.mk'_surjective _)).trans
    (normalizerInM g).card_subgroup_dvd_card

/-- The genuine action and torus geometry needed for the Fitting argument.
Every field requires a separate proof from the source inputs. -/
public structure ActionData (d : Context Z M z t m) (g : LocalGeometry Z M z t m) where
  action : quotient g →* MulAut (sylowImage d g)
  faithful : Function.Injective action
  conjugation : ∀ n : normalizerInM g, ∀ v : sylowImage d g,
    (action (projection g n) v : pointQuotient d) =
      pointProjection d (n : M) * (v : pointQuotient d) * (pointProjection d (n : M))⁻¹
  odd : Odd (Nat.card (quotient g))
  torus_cyclic : IsCyclic (torusImage g)
  torus_card : Nat.card (torusImage g) = 2 ^ (2 * m + 1) - 1
  element_centralizers : ∀ x ∈ torusImage g, x ≠ 1 →
    centralizer ({x} : Set (quotient g)) ≤ normalizer (torusImage g : Set (quotient g))
  torus_centralizer : centralizer (torusImage g : Set (quotient g)) = torusImage g

end BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer

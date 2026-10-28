module

public import Theory.Representation.BinaryQuarticMathieu.Transport
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition
public import Theory.Representation.BinaryQuarticMathieu.HexadCoverage

/-!
# The intrinsic binary quartic and the marked Witt configuration

`BinaryQuarticMathieu.quartic` is the literal alternating form on ten binary
coordinates. Its contraction-rank distribution is invariant under every linear
preserver. The 22 explicitly marked vectors span the whole space, and the
configuration transport maps its full linear stabilizer faithfully into the
repository's literal Mathieu design automorphism group. Rank recognition and
complete zero-sum hexad coverage are proved by the imported finite certificates.

Thus `quarticStabilizer_card_le` bounds the full stabilizer by 887040 without
extra premises. `calibrated_range_card_le` applies the same bound to any
independently constructed intrinsic action whose tensor is calibrated to this
quartic. It requires preservation by the whole acting group and does not
require faithfulness for the image bound.

The literal tensor and marking are documented in the source repository's
`Scratch/J4FleetGuidance/SeedCentralizer/README.md` and in
`BinaryQuarticMathieu/source/README.md`. The proof uses the existing
`Sporadic.Mathieu.m22DesignAut_order`, with no Janko-group hypotheses.
-/

public section

namespace BinaryQuarticMathieu

attribute [local irreducible] quartic

/-- The full quartic stabilizer acts on the literal Witt design. Both finite
certificates have been discharged. -/
noncomputable def quarticDesignAction :
    quarticStabilizer →* Sporadic.Mathieu.m22DesignAut :=
  quarticStabilizerToDesignAut rankDistribution_recognition mem_m22Blocks_iff_isHexad

/-- The intrinsic points span, so the full stabilizer's design action is faithful. -/
theorem quarticDesignAction_injective : Function.Injective quarticDesignAction :=
  quarticStabilizerToDesignAut_injective
    rankDistribution_recognition mem_m22Blocks_iff_isHexad

/-- Unconditional order bound for every linear preserver of the exact quartic. -/
theorem quarticStabilizer_card_le : Nat.card quarticStabilizer ≤ 887040 :=
  quarticStabilizer_card_le_of_certificates
    rankDistribution_recognition mem_m22Blocks_iff_isHexad

/-- The image of any representation preserving the quartic has order at most
887040. The acting group need not act faithfully. -/
theorem linearEquiv_range_card_le {G : Type*} [Group G]
    (ρ : G →* (U ≃ₗ[F] U)) (hρ : ∀ g, Preserves quartic (ρ g)) :
    Nat.card ρ.range ≤ 887040 :=
  linearEquiv_range_card_le_of_certificates ρ hρ
    rankDistribution_recognition mem_m22Blocks_iff_isHexad

/-- Image bound for an intrinsic action on an arbitrary vector space, using its
actual tensor and an explicit calibration to the literal binary quartic.
Preservation is required for every element of the acting group. -/
theorem calibrated_range_card_le {G V : Type*} [Group G]
    [AddCommGroup V] [Module F V]
    (ρ : G →* (Module.End F V)ˣ) (b : V ≃ₗ[F] U)
    (Q : V [⋀^Fin 4]→ₗ[F] F)
    (hcalibration : ∀ v w x y, quartic ![b v, b w, b x, b y] = Q ![v, w, x, y])
    (hρ : ∀ g v w x y,
      Q ![(ρ g).val v, (ρ g).val w, (ρ g).val x, (ρ g).val y] = Q ![v, w, x, y]) :
    Nat.card ρ.range ≤ 887040 :=
  calibrated_range_card_le_of_certificates ρ b Q hcalibration hρ
    rankDistribution_recognition mem_m22Blocks_iff_isHexad

end BinaryQuarticMathieu

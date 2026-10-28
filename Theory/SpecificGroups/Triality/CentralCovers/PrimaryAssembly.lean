module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.GroupTheory.CoveringKernelBound

/-!
# Combining the two primary parts of the binary triality multiplier

The genuine binary carrier is finite, perfect, simple and centerless. The
canonical universal covering group therefore is finite quasisimple, and its
literal central quotient is isomorphic to that carrier. A two-group-center
theorem for arbitrary triality covers applies to precisely this quotient.
Its center is the canonical covering kernel. Excluding two from the order
of that kernel then makes the whole kernel trivial.

The odd-part input has the exact contract of
`Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers`; no
duplicate odd-prime calculation is required. Both primary inputs remain
explicit here, and exponent one is included throughout.

Source: GLS3 §6.1, Theorem 6.1.4 and Tables 6.1.2–3, as used in
Aschbacher–Smith I.1.3, printed p.407.
-/

public section

namespace Triality.Standard.CentralCovers

open Theory.GroupTheory PerfectCentralCovering

/-- Quasisimplicity of the genuine finite carrier, including `³D₄(2)`. -/
theorem isQuasisimple (n : ℕ) (hn : 0 < n) : IsQuasisimple (BinaryCarrier n hn) where
  toIsPerfect := inferInstance
  simple := by
    exact ((QuotientGroup.quotientMulEquivOfEq (binaryCarrier_center_eq_bot n hn)).trans
      QuotientGroup.quotientBot).isSimpleGroup

/-- The existing odd-center contract applies to the actual universal cover;
the independent two-primary exclusion completes the kernel calculation. -/
theorem universalProjection_ker_eq_bot_of_primary_calculations (n : ℕ) (hn : 0 < n)
    (hodd : ∀ (R : Type) [Group R] [Finite R] [IsQuasisimple R],
      IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R) →
      IsPGroup 2 (Subgroup.center R))
    (htwo : ¬ 2 ∣ Nat.card (universalProjection (BinaryCarrier n hn)).ker) :
    (universalProjection (BinaryCarrier n hn)).ker = ⊥ := by
  let G := BinaryCarrier n hn
  let : IsQuasisimple G := isQuasisimple n hn
  let e : UniversalGroup G ⧸ Subgroup.center (UniversalGroup G) ≃* G :=
    (universalCover G).quotientCenterEquiv.trans
      ((QuotientGroup.quotientMulEquivOfEq (binaryCarrier_center_eq_bot n hn)).trans
        QuotientGroup.quotientBot)
  have hmodel : IsTrialityGroupAt (2 ^ n)
      (UniversalGroup G ⧸ Subgroup.center (UniversalGroup G)) :=
    (isTrialityGroupAt_binary_iff _ n hn).mpr ⟨e⟩
  have hcenter := hodd (UniversalGroup G) hmodel
  have heq : (universalProjection G).ker = Subgroup.center (UniversalGroup G) :=
    (universalQuasisimpleCover G).ker_eq_center_of_isSimple
  have hker : IsPGroup 2 (universalProjection G).ker := by
    rw [heq]
    exact hcenter
  rcases hker.card_eq_or_dvd with hc | hd
  · exact Subgroup.card_eq_one.mp hc
  · exact (htwo hd).elim

end Triality.Standard.CentralCovers

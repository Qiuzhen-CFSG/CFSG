module
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.LongRoots
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.ShortRoots.Lifts

/-!
# The four polynomial exchanges for normalized triality sections

For q ≥ 4, the four short-root exchanges hold in any surjective central
extension whose additive sections are torus normalized and satisfy the ten
commuting relations. First the central torus removes the two trace defects.
The actors with fixed-field parameters (c,c) and (c²,c³) then fix short root 1
and long root 0, respectively, while scaling short root 0 by c ≠ 1.
The trace exchanges make the two polynomial candidate words additive, so
scalar-equivariant uniqueness removes their central defects as well.

All coefficients are computed in the actual D₄ marking, including the
vanishing highest-long term in the short0/long0 exchange. The argument
includes q = 4 and never asks that c³ ≠ 1. The commuting relations remain an
explicit premise, to be discharged by their independent producer.

Sources: GLS3 §2.4.5(b), §2.4.7 and §6.1; Aschbacher–Smith A.2.4 and I.1.3
(`refs/quasithin.pdf`, PDF pp.44 and 418).
-/

public section
namespace Triality.Standard.CentralCovers.TwoPrimary
open Parabolics PerfectCentralCovering
variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]
variable {f : E →* BinaryCarrier n hn}

/-- All four literal triality exchanges, with only the commuting family
retained as an independent inter-root hypothesis. -/
theorem RootSections.normalized_short_exchanges (L : RootSections n hn f)
    (hL : L.TorusNormalized) (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hC : L.CommutingRelations) : L.ShortExchangeRelations := by
  obtain ⟨c, hc⟩ := RootSections.ShortPolynomial.exists_unit (hn := hn) hlarge
  have h02 := RootSections.ShortPolynomial.lift_trace L hL hC hf hk c hc 0
  have h12 := RootSections.ShortPolynomial.lift_trace L hL hC hf hk c hc 1
  have h01 := RootSections.ShortPolynomial.lift01 L hL hC hf hk c hc h02
  exact ⟨RootSections.ShortPolynomial.lift00 L hL hC hf hk c hc h02 h12 h01,
    h01, h02, h12⟩

/-- The literal unipotent inclusion splits using the proved exchanges;
the supplied commuting family is the sole remaining inter-root input. -/
theorem RootSections.exists_unipotent_section_of_normalized_commuting
    (L : RootSections n hn f) (hL : L.TorusNormalized) (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hC : L.CommutingRelations) :
    ∃ s : unipotent (binaryParameters n hn) →* E,
      f.comp s = (unipotent (binaryParameters n hn)).subtype :=
  L.exists_unipotent_section (L.higherCommutators_of_relations hC
    (L.normalized_short_exchanges hL hlarge hf hk hC)
    (L.normalized_long_exchange hL hlarge hf hk))

/-- Specialization to the actual canonical cover, including the field of
order four, under the independently supplied commuting relations. -/
theorem universal_not_two_dvd_kernel_of_normalized_commuting
    (n : ℕ) (hn : 0 < n) (hlarge : 2 ≤ n)
    (L : RootSections n hn (universalProjection (BinaryCarrier n hn)))
    (hL : L.TorusNormalized) (hC : L.CommutingRelations) :
    ¬ 2 ∣ Nat.card (universalProjection (BinaryCarrier n hn)).ker := by
  have hf := universalProjection_surjective (BinaryCarrier n hn)
  have hk := universalProjection_ker_le_center (BinaryCarrier n hn)
  exact universal_not_two_dvd_kernel_of_higherCommutators n hn L
    (L.higherCommutators_of_relations hC (L.normalized_short_exchanges hL hlarge hf hk hC)
      (L.normalized_long_exchange hL hlarge hf hk))
end Triality.Standard.CentralCovers.TwoPrimary

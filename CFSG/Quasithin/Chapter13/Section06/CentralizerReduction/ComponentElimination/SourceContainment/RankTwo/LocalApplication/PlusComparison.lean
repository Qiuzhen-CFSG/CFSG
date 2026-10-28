module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.Maps
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison

/-!
# The central quotient of the actual plus image

Yz supplies quasisimplicity of K*/O₂(K*). The R₂ conclusion of B.2.14
supplies O₂(G+)=1. The established surjection from that star quotient
to K+ therefore compares their central quotients, compatibly with every
element of the original K. This proves the plus side of the comparison
without assuming quasisimplicity of K/O₂(K).

The separate Intrinsic and Localization modules construct a C-component
in KLᵥ and establish the intrinsic two-core quotient's quasisimplicity.
No equality of the star, plus and prime-complement kernels is asserted.
Source: Aschbacher–Smith, combined manuscript, pp.929–931, and A.3.18,
pp.51–53.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

section Plus
variable (K L T : Subgroup G) (z v : G)
  (hL : Tv T v ≤ normalizer (Lv L v : Set G))
  (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
  (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)

/-- The literal star two-core quotient and its plus image have the same
central quotient, through the already constructed quotient homomorphism. -/
noncomputable def starPlusCentralQuotientEquiv :
    ((starImage z v K ⧸ pCore 2 (starImage z v K)) ⧸
      center (starImage z v K ⧸ pCore 2 (starImage z v K))) ≃*
    (plusImage K L T z v hL hz K ⧸ center (plusImage K L T z v hL hz K)) := by
  let := hK.2.1
  let : Nontrivial (plusImage K L T z v hL hz K) :=
    (nontrivial_iff_ne_bot _).mpr (plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK)
  exact IsQuasisimple.centralQuotientEquiv
    (componentCoreQuotientToPlus K L T z v hL hz hK hR)
    (componentCoreQuotientToPlus_surjective K L T z v hL hz hK hR)

/-- Compatibility holds on representatives from the original K. -/
theorem starPlusCentralQuotientEquiv_mk (k : K) :
    starPlusCentralQuotientEquiv K L T z v hL hz hK hR
      (QuotientGroup.mk' (center (starImage z v K ⧸ pCore 2 (starImage z v K)))
        (QuotientGroup.mk' (pCore 2 (starImage z v K)) (starImageMap z v K hK.1.1 k))) =
      QuotientGroup.mk' (center (plusImage K L T z v hL hz K))
        (toPlusImage K L T z v hK.1.1 hL hz k) := rfl

include hR in
/-- The intrinsic O₂(K) is killed by the literal map to K+. -/
theorem toPlusImage_twoCore_le_ker :
    pCore 2 K ≤ (toPlusImage K L T z v hK.1.1 hL hz).ker := by
  have he : pCore 2 (plusImage K L T z v hL hz K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal K L T z v hL hz hK), hR]
    exact (MonoidHom.ker_eq_bot_iff _).mpr
      (plusImage K L T z v hL hz K).subtype_injective
  let f := toPlusImage K L T z v hK.1.1 hL hz
  have hm : (pCore 2 K).map f ≤ pCore 2 (plusImage K L T z v hL hz K) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance f
      (toPlusImage_surjective K L T z v hK.1.1 hL hz), pCore_isPGroup.map f⟩
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (hm.trans he.le))

/-- The intrinsic two-core quotient surjects onto K+, before any assertion
that the source of this map is quasisimple. -/
noncomputable def intrinsicTwoCoreToPlus :
    (K ⧸ pCore 2 K) →* plusImage K L T z v hL hz K :=
  QuotientGroup.lift _ (toPlusImage K L T z v hK.1.1 hL hz)
    (toPlusImage_twoCore_le_ker K L T z v hL hz hK hR)

theorem intrinsicTwoCoreToPlus_surjective :
    Function.Surjective (intrinsicTwoCoreToPlus K L T z v hL hz hK hR) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    (toPlusImage_surjective K L T z v hK.1.1 hL hz) _

theorem intrinsicTwoCoreToPlus_mk (k : K) :
    intrinsicTwoCoreToPlus K L T z v hL hz hK hR (QuotientGroup.mk' (pCore 2 K) k) =
      toPlusImage K L T z v hK.1.1 hL hz k := rfl

end Plus

/-- The rank-two branch's local image survives the prime-complement quotient.
This uses divisibility, without assuming any local component conclusion. -/
theorem localImage_nontrivial (K L : Subgroup G) (v : G) (hr : primeRank 3 K = 2) :
    Nontrivial (localImage K L v) := by
  apply threePrime_image_nontrivial
  apply Classical.byContradiction
  intro h
  have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr h
  rw [localComponent_rank K L v, hr] at hz
  omega

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication

module

public import CFSG.Quasithin.ChapterF.Section06.Elementary
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.SmallPrimes
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.PerfectCentralCoverOddPart
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ThreeResidual
/-!
# The J₁ exception in the cyclic component branch

The actual cubic normalizer bounds in J₁ rule out normalization by a
Sylow two-subgroup. The original Goldschmidt intersection supplies that
Sylow subgroup and its action on the contained cubic local residual.
For the central-quotient version, the source O₃′ quotient makes the
component center a three-group, and cyclic Sylow transfer excludes three
from the kernel of its actual perfect central cover of J₁.

Source: Aschbacher–Smith, F.6.17, printed p.309; I.1.3, printed p.407.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ K : Subgroup G}

/-- A Sylow-normalized cubic subgroup cannot occur in the actual J₁ model. -/
theorem not_janko_one_of_sylow_normalizes_cubic
    (S : Sylow 2 G) (A : Subgroup G) (hA : Nat.card A = 3)
    (hSA : (S : Subgroup G) ≤ normalizer (A : Set G)) :
    ¬ Nonempty (G ≃* Janko1.Model) := by
  rintro ⟨e⟩
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcardT : Nat.card T = 8 := Janko1.SylowTwo.card T
  have hcardA : Nat.card (A.map e.toMonoidHom) = 3 :=
    (card_map_of_injective e.injective).trans hA
  apply Janko1.LocalStructure.primeNormalizerBound_three _ hcardA
  rw [← hcardT]
  apply card_dvd_of_le
  change (S : Subgroup G).map e.toMonoidHom ≤ _
  rw [← map_equiv_normalizer_eq A e]
  exact map_mono hSA

/-- For the original local residual inside a component, the common Sylow
intersection is the actual Sylow subgroup normalizing that cubic group. -/
theorem component_not_janko_one_of_left_residual_cubic
    (h : IsGoldschmidtTriple G₁ G₂) (hK : IsComponent G K)
    (hL : (pResidual 2 G₁).map G₁.subtype ≤ K)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    ¬ Nonempty (K ≃* Janko1.Model) := by
  let A := (pResidual 2 G₁).map G₁.subtype
  obtain ⟨S, hS⟩ := h.subnormal_intersection_sylow K hK.1
  have hcard : Nat.card (A.subgroupOf K) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hL).toEquiv).trans hc
  apply not_janko_one_of_sylow_normalizes_cubic S (A.subgroupOf K) hcard
  apply le_normalizer_iff.mpr
  intro s hs a ha
  change (s : G) * (a : G) * (s : G)⁻¹ ∈ A
  rw [hS] at hs
  exact (mem_normalizer_iff.mp (h.intersection_normalizes_left_residual hs) (a : G)).mp ha

/-- Every ordinary component in the original O₃′ quotient has three-group center. -/
theorem component_center_is_three_group
    {H : Type*} [Group H] [Finite H] (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G K) : IsPGroup 3 (center K) := by
  let : IsQuasisimple K := hK.2
  have hcore := Subgroup.IsSubnormal.pPrimeCore_eq_bot
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient e) K hK.1
  rw [IsQuasisimple.center_eq_pCore hcore]
  exact pCore_isPGroup

/-- The actual central projection onto J₁ is an isomorphism in the F.6 source quotient. -/
noncomputable def janko_component_equiv_of_central_quotient
    {H : Type*} [Group H] [Finite H] (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G K) (j : (K ⧸ center K) ≃* Janko1.Model) :
    K ≃* Janko1.Model := by
  let : IsQuasisimple K := hK.2
  let f := PerfectCentralCovering.centralQuotientCover j
  have hp : IsPGroup 3 f.toMonoidHom.ker := by
    rw [PerfectCentralCovering.centralQuotientCover_ker]
    exact component_center_is_three_group e hK
  have hnot : ¬ 3 ∣ Nat.card f.toMonoidHom.ker :=
    f.not_dvd_card_kernel_of_square_not_dvd (by norm_num [Janko1.card_model])
  have hc : Nat.card f.toMonoidHom.ker = 1 := hp.card_eq_or_dvd.resolve_right hnot
  exact MulEquiv.ofBijective f.toMonoidHom
    ⟨f.toMonoidHom.ker_eq_bot_iff.mp (Subgroup.card_eq_one.mp hc), f.surjective⟩

/-- The J₁ central-quotient option is excluded using the original cubic local
residual, the actual Sylow intersection and the proved central-cover descent. -/
theorem central_quotient_not_janko_one_of_left_residual_cubic
    {H : Type*} [Group H] [Finite H] (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂) (hK : IsComponent G K)
    (hL : (pResidual 2 G₁).map G₁.subtype ≤ K)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    ¬ Nonempty ((K ⧸ center K) ≃* Janko1.Model) := by
  rintro ⟨j⟩
  exact component_not_janko_one_of_left_residual_cubic h hK hL hc
    ⟨janko_component_equiv_of_central_quotient e hK j⟩
end CFSG.Quasithin.ChapterF.SourceAssembly

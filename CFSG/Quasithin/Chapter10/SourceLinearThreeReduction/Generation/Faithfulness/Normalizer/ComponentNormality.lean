module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.NonnormalRankOne
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.OddPSL2Components
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.UnitaryComponents
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.Centered
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.ClassicalInputs
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.RemainingRows

/-!
# Normality of the escaping odd-normalizer component

A nonnormal component with nontrivial center has a binary unitary-three
central quotient, incompatible with the perfect residual's noncentral
two-core projection. The remaining centerless component has the additive
local-plus-ordinary odd-rank budget. The proved five-row catalogue and
perfect-core exclusions then force normality. These arguments use the
original module and residual and require no A₅ quotient marking.

The trivial two-core premise remains explicit: its source C.4.8 discharge
belongs to qt-d-10-nona5-hall-faithfulness, as does the subsequent placement
of the fixed residual in this normal component.
Source: Aschbacher--Smith, 4.4.9--11, printed p.621, using A.3.8,
printed pp.45--46 (combined manuscript of 1 March 2004).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.QTComponents
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual escaping component is normal once the normalizer two-core
has been excluded. All catalogue and outer-action inputs are discharged. -/
theorem source_oddNormalizer_component_normal_of_twoCore
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hcore : pCore 2 (normalizer (B : Set G)) = ⊥)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) :
    K.Normal := by
  classical
  by_contra hnK
  obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK D.simpleQTKE B hne
  have hz : center K = ⊥ := by
    by_contra hz
    obtain ⟨n,hn,_,hm⟩ := nonnormal_centered_projectiveUnitary hqt hkg hcore K hK hnK hz
    exact source_oddNormalizer_no_binary_unitary_nonnormal_component D B hne
      hBC hodd hBV K hK hnK houtK (by omega) hm hFK
  let j : (K ⧸ center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  have hr : OddRankBudget K := fun r hp ho =>
    hK.local_add_ordinary_rank_le_two_of_nonnormal_centerless hqt hnK hz r hp ho
  have hb : OddRankBudget (K ⧸ center K) := OddRankBudget.of_mulEquiv hr j
  have hm := nonnormal_model_of_budget_of_remaining_local remainingLocalInput hb
    (nonnormal_centralQuotient_model hqt hkg K hK hnK)
  cases hm with
  | linear_even n hn he =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    exact source_oddNormalizer_no_sl2_nonnormal_component D B hne hBC hodd hBV
      K hK hnK houtK e hFK
  | suzuki m hm he =>
    exact source_oddNormalizer_no_suzuki_nonnormal_component D B hne hBC hodd hBV
      K hK hnK houtK hm he.some hFK
  | linear_odd q ho he =>
    exact source_oddNormalizer_no_odd_psl2_model_nonnormal_component D B hne hBC hodd hBV
      K hK hnK houtK ho he hFK
  | janko he =>
    exact source_oddNormalizer_no_janko_nonnormal_component D B hne hBC hodd hBV
      K hK hnK houtK he.some hFK
  | unitary n hn he =>
    exact source_oddNormalizer_no_binary_unitary_nonnormal_component D B hne hBC hodd hBV
      K hK hnK houtK hn he hFK

end CFSG.Quasithin.Chapter10

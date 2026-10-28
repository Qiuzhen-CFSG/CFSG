module
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.ClassicalInputs
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.NonnormalCenter
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.NonnormalRankOne
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.OddPSL2Components

/-!
# Normality of the original escaping component from local cubic ranks

The centered branch is already excluded on the actual Hall data. For a
nonnormal component its centerless central quotient satisfies the additive
local-plus-ordinary rank budget and the full Theorem C catalogue. The
five-row inspection and the proved perfect-core exclusions then contradict
nonnormality. The general assembly retains three independent model-local
families; the final wrapper discharges both classical families and retains
only positive local cubic ranks for the remaining finite and binary rows.
All original source data and literal central-quotient maps are unchanged.

Source: Aschbacher–Smith4.4.9–11, p.621, using A.3.8(1–2), pp.45–46.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterA.QTComponents
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual nonnormal component has the five-row central-quotient model,
conditional only on the three independent model-local source families. -/
theorem source_a5_oddNormalizer_nonnormal_component_model_of_row_inputs
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hodd : OddThreeBudgetInput (K ⧸ center K))
    (hbinary : BinaryThreeBudgetInput (K ⧸ center K))
    (hlocal : RemainingLocalInput (K ⧸ center K)) :
    NonnormalModel (K ⧸ center K) := by
  obtain ⟨hz,hr⟩ := source_a5_oddNormalizer_nonnormal_component_rank_budget
    D e hn hp B hne hB hBC hBV hperm K hK hnK houtK hFK
  let j : (K ⧸ center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  have hb : OddRankBudget (K ⧸ center K) := OddRankBudget.of_mulEquiv hr j
  obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK D.simpleQTKE B hne
  exact nonnormal_model_of_budget hodd hbinary hlocal hb
    (ChapterA.QTComponents.nonnormal_centralQuotient_model hqt hkg K hK hnK)

/-- The original escaping component is normal once the three independent
model-local source inputs are supplied. -/
theorem source_a5_oddNormalizer_component_normal_of_row_inputs
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hodd : OddThreeBudgetInput (K ⧸ center K))
    (hbinary : BinaryThreeBudgetInput (K ⧸ center K))
    (hlocal : RemainingLocalInput (K ⧸ center K)) : K.Normal := by
  classical
  by_contra hnK
  have hm := source_a5_oddNormalizer_nonnormal_component_model_of_row_inputs
    D e hn hp B hne hB hBC hBV hperm K hK hnK houtK hFK hodd hbinary hlocal
  have hBodd : Odd (Nat.card B) := by
    obtain ⟨n,hnn⟩ := hB.exists_card_eq
    rw [hnn]
    exact hp.pow
  cases hm with
  | linear_even n hn he =>
    obtain ⟨F,_,_,hc,⟨j⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    exact source_oddNormalizer_no_sl2_nonnormal_component D B hne hBC hBodd hBV
      K hK hnK houtK j hFK
  | suzuki m hm he =>
    exact source_oddNormalizer_no_suzuki_nonnormal_component D B hne hBC hBodd hBV
      K hK hnK houtK hm he.some hFK
  | linear_odd q ho he =>
    exact source_oddNormalizer_no_odd_psl2_model_nonnormal_component D B hne hBC hBodd hBV
      K hK hnK houtK ho he hFK
  | janko he =>
    exact source_oddNormalizer_no_janko_nonnormal_component D B hne hBC hBodd hBV
      K hK hnK houtK he.some hFK
  | unitary n hn he =>
    exact source_oddNormalizer_no_binary_unitary_nonnormal_component D B hne hBC hBodd hBV
      K hK hnK houtK hn he hFK

/-- The odd and binary degree-three families are discharged; the remaining
finite and binary local cubic ranks are the only explicit model input. -/
theorem source_a5_oddNormalizer_component_normal_of_remaining_local
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hlocal : RemainingLocalInput (K ⧸ center K)) : K.Normal := by
  exact source_a5_oddNormalizer_component_normal_of_row_inputs
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
    oddThreeBudgetInput binaryThreeBudgetInput hlocal

end CFSG.Quasithin.Chapter10

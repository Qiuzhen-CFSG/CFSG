module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.QuotientBasisSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.OutsideFixedSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.Geometry
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.OuterPairSource

/-!
# Thompson stability in the original double linear branch

The paired outer action gives two-rank at most two for H/L₀ and at most
three for M₀/J(S). An outside involution fixes rank at most 2n in J(S),
whereas the actual elementary core has order 2^(4n). For n≥2 these bounds
exclude a maximum elementary subgroup outside S, so J(M₀)=J(S).
The original torus constructor discharges every geometric input.

Source: Aschbacher--Smith, proof of 2.4.7, printed p.540.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter2
open LinearDouble ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}

omit [Finite G] in
/-- The actual two-core has the full four-natural-coordinate cardinality. -/
theorem LinearDouble.SourceTorusData.core_card
    {c : DoubleLinearSourceSetup d M₀ n} (td : SourceTorusData c)
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n) :
    Nat.card (twoCore d.H) = 2^(4*n) := by
  let U₁ := sourceModule (d.block.map d.H.subtype)
  let U₂ := sourceModule c.second
  have h₁ : Nat.card U₁ = 2^(2*n) :=
    RankOne.card_U_of_center_eq_bot hL td.geometry.centerless_first
  have h₂ : Nat.card U₂ = 2^(2*n) :=
    RankOne.card_U_of_center_eq_bot c.second_type td.geometry.centerless_second
  have hU₁ : U₁ ≤ d.block.map d.H.subtype := map_subtype_le _
  have hU₂ : U₂ ≤ c.second := map_subtype_le _
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting U₁ U₂
    (td.geometry.blocks_disjoint.mono hU₁ hU₂)
    (hU₁.trans ((le_centralizer_iff.mp c.commutes).trans (centralizer_le hU₂)))
  rw [td.geometry.core,←Nat.card_congr e.toEquiv,Nat.card_prod,h₁,h₂,←pow_add]
  congr 1
  omega

/-- The source cardinal witness and actual outside fixed-point bounds
make the Thompson subgroup unchanged in the prescribed index-two overgroup. -/
theorem LinearDouble.SourceTorusData.thompson_eq_of_residual_quotient_rank
    {c : DoubleLinearSourceSetup d M₀ n} (td : SourceTorusData c)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hquot : let : d.L0.Normal := d.L0_normal; primeRank 2 (d.H ⧸ d.L0) ≤ 2) :
    Stellmacher.elementaryAbelianMaxJ M₀ =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let : (R.subgroupOf M₀).Normal := normal_subgroupOf_of_le_normalizer
    (c.original.R_normal.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ S))
  apply thompson_eq_of_rank_bounds M₀ S R c.original.R_le_M hL.1
    (td.overgroup_quotient_rank hi hquot)
    (fun a ha haS ha2 => td.outside_fixed_rank hL hi a ha haS ha2)
    (twoCore d.H) (pCoreIn_le_sylow d.H d.S)
    (gammaEvenZero_twoCore_elementary_source hG T hTM hu d.mem_gammaEvenZero)
    (td.core_card hL)
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
open LinearDouble
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}

/-- The actual residual outer action has two-rank at most two. -/
theorem LinearDouble.SourceTorusData.residual_quotient_rank
    {c : DoubleLinearSourceSetup d M₀ n} (td : SourceTorusData c)
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n) :
    let : d.L0.Normal := d.L0_normal
    primeRank 2 (d.H ⧸ d.L0) ≤ 2 := by
  let : d.L0.Normal := d.L0_normal
  let B := normalizer (d.block : Set d.H)
  let : B.Normal := normal_of_index_eq_two c.parabolic_stabilizer_index
  obtain ⟨hC,f,hNf,hsep⟩ := c.outer_pair td hL
  let := hC
  exact primeRank_quotient_le_two_of_cyclic_pair B d.L0
    c.parabolic_stabilizer_index c.residual_le_parabolic_stabilizer f hNf hsep

/-- Thompson stability uses only the original marked double-linear hypotheses. -/
theorem DoubleLinearSourceSetup.thompson_eq_from_original
    (c : DoubleLinearSourceSetup d M₀ n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀) (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    Stellmacher.elementaryAbelianMaxJ M₀ =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  obtain ⟨td⟩ := c.torus_data hG T hM hTM hu hST hL hSM hMT hi
  exact td.thompson_eq_of_residual_quotient_rank hG T hTM hu hL hi
    (td.residual_quotient_rank hL)
end CFSG.Quasithin.Chapter2

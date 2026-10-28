module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.CubicComponent
public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.Mathieu.M24.Properties.CubicElementary
public import Theory.Mathieu.M24.Properties.Sylow3
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.Mathieu.SchurMultipliers.Models
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# The native Mathieu twenty-four row of the paired alternating-five argument

The actual opposite block supplies a cubic centralizing the selected deleted
module. The component residual theorem places it inside the marked ordinary
component, and the faithful two-core quotient preserves the elementary subgroup
of order sixteen. Native M24 cubic fusion excludes that centralization.

Source: Aschbacher--Smith 2.4.25, printed pp.542--543. All component, quotient,
and module markings are inherited from the original paired-block configuration.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G]
variable {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

private theorem m24_three_rank_ge_two : 2 ≤ primeRank 3 M24 := by
  by_contra hh
  have hr : primeRank 3 M24 ≤ 1 := by omega
  let : IsCyclic m24Sylow3 :=
    m24Sylow3.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  have ha : IsMulCommutative m24Sylow3Subgroup := by
    rw [← m24Sylow3_coe]
    infer_instance
  exact m24Sylow3Subgroup_isNonabelian ha

/-- The M24 row for the literal ordinary component of the original Phi normalizer. -/
theorem AlternatingPairSourceSetup.mathieu24_overcomponent_false
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
      SI S L ≤ normalizer (K.map GI.subtype : Set G) →
      Nonempty ((K ⧸ pCore 2 K) ≃* ClassificationModels.SporadicName.m24.Carrier) → False := by
  intro S L GI K hK hLK _ hm
  change Nonempty ((K ⧸ pCore 2 K) ≃* M24) at hm
  exact c.cubic_centralizer_overcomponent_false (D := M24)
    hG T hM hTM hu hST hSM hMT hi
    M24InvolutionCentralizers.center_eq_bot m24_three_rank_ge_two
    M24OuterRestriction.outer_isPGroup_two
    (fun E hE hc b hb hEB => by
      let : IsElementaryAbelian 2 E := hE
      exact M24CubicElementary.not_centralizes_elementary_sixteen E hc b hb hEB)
    K hK hLK hm

end CFSG.Quasithin.Chapter2

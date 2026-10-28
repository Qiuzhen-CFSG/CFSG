module
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.InnerEvenQuotientEscape
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LargeSporadic.JankoFour.Placement
public import Theory.SpecificGroups.Janko4.Model.OddLocalRanks
public import Theory.GroupTheory.OddPrimeRankOneSylow
/-! The original paired setup in the J4 quotient produces an even
centralizer by its opposite cubic. Native involution-centralizer placement
preserves the exact normalizer Sylow, and the first local obstruction is
unconditional. This assembly isolates only the second centralizer's local
alternating-five obstruction, supplied by its elementary-kernel action.
No covering-isomorphism or abstract A5 placement is assumed.
Source: Aschbacher--Smith 2.4.25, printed pp.542--543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}
private theorem j4_three_rank_ge_two : 2 ≤ primeRank 3 Janko4.Model := by
  by_contra hh
  have hr : primeRank 3 Janko4.Model ≤ 1 := by omega
  let P := Janko4.Simplicity.threeLocalSubgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  have hc : Nat.card P = 3^3 := Janko4.Simplicity.threeLocal_card _ _
  obtain ⟨Q,hPQ⟩ := (IsPGroup.of_card hc).exists_le_sylow
  let : IsCyclic Q := Q.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  exact Janko4.Simplicity.threeLocal_not_isMulCommutative _ _
    (IsMulCommutative.of_setLike_mul_comm fun x hx y hy =>
      (isMulCommutative_iff_of_setLike.mp (inferInstance : IsMulCommutative Q))
        x (hPQ hx) y (hPQ hy))

theorem AlternatingPairSourceSetup.j4_overcomponent_false_of_second
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
    (∀ A : Subgroup Janko4.InvolutionCentralizers.Second.ambientCentralizer,
      IsAlternatingBlock A 5 → Nat.card ((blockU A).map A.subtype) = 16 →
      ∀ S : Sylow 2 Janko4.InvolutionCentralizers.Second.ambientCentralizer,
        A ∉ ChapterA.Section03.localCComponents S) →
    Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) → False := by
  intro S L GI K hK hLK hNK hsecond ⟨e⟩
  let : IsQuasisimple K := hK.2
  have hnon : ¬IsMulCommutative Janko4.Model := by
    intro hh
    let : IsMulCommutative Janko4.Model := hh
    exact Janko4.Simplicity.threeLocal_not_isMulCommutative
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four inferInstance
  let : Nontrivial Janko4.Model := not_subsingleton_iff_nontrivial.mp (fun hh => by
    let : Subsingleton Janko4.Model := hh
    exact hnon inferInstance)
  let : IsQuasisimple Janko4.Model := IsQuasisimple.of_surjective
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact c.inner_even_quotient_overcomponent_false hG T hM hTM hu hST hSM hMT hi
    K hK hLK hNK Janko4.model_center_eq_bot j4_three_rank_ge_two
    Janko4.AdequateLocal.outer_isPGroup_two Janko4.AdequateLocal.conj_surjective
    (AlternatingTerminal.JankoFour.even_centralizer_escape_of_second hsecond) ⟨e⟩
end CFSG.Quasithin.Chapter2

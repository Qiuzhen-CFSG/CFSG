module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NormalizerSource
public import CFSG.Quasithin.ChapterC.Section06.CentralizerRank
/-!
# Centralizer ranks for the original single-block shadows

The actual selected block produces the original C.5 configuration, its
marked action, and an escaping conjugator. The proved C.6 rank bounds
therefore apply to the centralizer in the literal selected Sylow image.
No field marking, disjointness, or core identity is assumed here.

Source: Aschbacher--Smith 2.4.5(3), 2.4.8 and C.6.1(3), pp.528--530,164--165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_natural_centralizer_rank
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    {n : ℕ} (hK : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n) :
    let D := (d.S : Subgroup d.H).map d.H.subtype ⊓
      centralizer (d.block.map d.H.subtype : Set G)
    IsElementaryAbelian 2 D ∧ Nat.card D ≤ 2 ^ n ∧ primeRank 2 D ≤ n := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c,F,hF,h,x,hx,hnc⟩ := d.single_rankOne_configuration hG T hST.le hsingle
    (Or.inl ⟨n,hK⟩) M₀ hSM hMT hi
  exact ChapterC.Section06.natural_centralizer_rank_from_original c h hK hi x hx hnc

theorem MinimalBlockSetup.single_cubic_centralizer_rank
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3) :
    let D := (d.S : Subgroup d.H).map d.H.subtype ⊓
      centralizer (d.block.map d.H.subtype : Set G)
    IsElementaryAbelian 2 D ∧ Nat.card D ≤ 2 ∧ primeRank 2 D ≤ 1 := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c,F,hF,h,x,hx,hnc⟩ := d.single_rankOne_configuration hG T hST.le hsingle
    (Or.inr hK) M₀ hSM hMT hi
  exact ChapterC.Section06.cubic_centralizer_rank_from_original c h hK hi x hx hnc

end CFSG.Quasithin.Chapter2

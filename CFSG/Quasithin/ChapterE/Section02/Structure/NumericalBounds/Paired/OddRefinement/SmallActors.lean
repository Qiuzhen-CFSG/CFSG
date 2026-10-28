module

public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.EscapeGeneration
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.CentralizerReduction

/-!
# Rank-one escape for small swapping actors

The swapping involution centralizes the actual norm diagonal and the
original tau. It therefore lies in the solvable radical of their join.
For an elementary actor of order at most four, killing that involution
leaves quotient rank at most one. The genuine norm-tau E-member thus has
degree one. If the factor stabilizer centralizes the component, the proved
full-orbit rank-one branch applies instead.

The final theorem retains the original core-free minimal parabolic and
returns an actual escaping E-member. The order bound is essential for this
argument: an order-eight actor can retain a four-group after killing the swap.
This theorem does not establish odd-prime paired generation at one for all
families. Source: Aschbacher–Smith E.1.2, E.1.11 and E.2.2, pp.210,213–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired.OddRefinement
variable {G : Type*} [Group G] [Finite G]

theorem norm_tau_member_one_of_card_le_four
    (T : Sylow 2 G) {K A : Subgroup G} (hK : IsComponent G K) [IsSimpleGroup K]
    (hcore : pCore 2 G = ⊥) (hindex : (normalizer (K : Set G)).index = 2)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    {a : G} (ha : a ∈ A) (hm : K.map (MulAut.conj a).toMonoidHom ≠ K)
    (hne : ¬ A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G))
    (hcard : Nat.card A ≤ 4) :
    IsEMemberAt 1 (T : Subgroup G) A
      (NormPair.normRange hK hm ⊔ tau (T : Subgroup G) A) := by
  let I := NormPair.normRange hK hm
  let X := I ⊔ tau (T : Subgroup G) A
  have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hXC : X ≤ centralizer ({a} : Set G) := by
    apply sup_le (componentSwapNorm_range_le_centralizer hK hm ha2)
    intro t ht
    have hc := (mem_centralizerModulo_iff.mp ht).2 a ha
    rw [hcore,mem_bot,commutatorElement_eq_one_iff_mul_comm] at hc
    exact mem_centralizer_singleton_iff.mpr hc.symm
  have ha1 : a ≠ 1 := by
    intro he
    apply hm
    subst a
    exact mem_normalizer_iff_map_conj_eq.mp ((normalizer (K : Set G)).one_mem)
  have h := PairedGeneration.SwappedActor.norm_tau_member T hK hcore hindex
    (show primeRank 2 (MulAut K) ≤ primeRank 2 (MulAut K) from le_rfl) hAT ha hm hne
  exact ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.isEMemberAt_of_central_actor
    (by decide) h.1 (IsElementaryAbelian.rank_le_of_card_le (p := 2) A hcard) ha ha1 hXC

theorem exists_small_moving_member_escape
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K A : Subgroup G} (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hn : ¬ K.Normal)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hmove : ¬ A ≤ normalizer (K : Set G)) (hcard : Nat.card A ≤ 4) :
    ∃ X : Subgroup G, IsEMemberAt 1 (T : Subgroup G) A X ∧
      ¬ X ≤ ChapterB.minimalParabolicMax T hP := by
  have hrad : solvableRadical G = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  have hcore := SimpleSocle.pCore_eq_bot hrad 2
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup K := isSimpleGroup_of_isQuasisimple_of_solvableRadical_eq_bot hrad hK.1
  have hi : (normalizer (K : Set G)).index = 2 := by
    rcases component_normal_or_pair hG T hK hgen with h | ⟨t,_,_,_,_,_,_,hi⟩
    · exact (hn h.1).elim
    · exact hi
  by_cases hfix : A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G)
  · have hl := residual_eq_layer T hK hgen
    have hra := rank_one_of_moved_pair_and_fixed_stabilizer T hK hgen hl hcore hi hAT hmove hfix
    have hAt : A ≤ tau (T : Subgroup G) A := le_sup_left.trans (sup_pCore_le_tau T A hAT)
    have ho := moved_pair_orbit_eq_residual T hK hgen hl hi
      (show ¬ tau (T : Subgroup G) A ≤ normalizer (K : Set G) from fun h => hmove (hAt.trans h))
    refine ⟨_,ChiefOrbit.tau_join_member_of_full_orbit T hK hrad hl hAT ho
      (.inr ⟨hmove,hra⟩) hra.le,?_⟩
    intro hx
    exact (ChapterB.minimalParabolicMax_spec T hP).1.ne_top
      (top_unique (hgen ▸ sup_le (le_sup_left.trans hx) (ChapterB.minimalParabolicMax_spec T hP).2))
  · obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hmove
    have hm : K.map (MulAut.conj a).toMonoidHom ≠ K :=
      fun h => han (mem_normalizer_iff_map_conj_eq.mpr h)
    exact ⟨_,norm_tau_member_one_of_card_le_four T hK hcore hi hAT ha hm hfix hcard,
      PairedGeneration.SwappedActor.norm_tau_not_le_minimalParabolicMax T hP hK hgen hm⟩

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired.OddRefinement

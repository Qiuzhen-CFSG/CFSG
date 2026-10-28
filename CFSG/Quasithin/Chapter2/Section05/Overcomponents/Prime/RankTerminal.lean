module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.PairedCentralizerSource
public import Theory.GroupTheory.PrimeRankProduct

/-! The final cubic-rank contradiction in source 2.5.19, printed p.564. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
open ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G]

private theorem rank_three_pos_of_dvd {A : Type*} [Group A] [Finite A]
    (hd : 3 ∣ Nat.card A) : 1 ≤ primeRank 3 A := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  let : IsElementaryAbelian 3 (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  by_contra hn
  have hh := (primeRank_le_iff_elementary_card_le A (p := 3) (n := 0)).mp
    (by omega) (zpowers x) inferInstance
  rw [Nat.card_zpowers,hx,pow_zero] at hh
  omega

/-- A centerless subgroup with an S₄ four-normalizer leaves at most one
cubic rank in its full ambient centralizer. The ambient rank bound is
applied only at the actual normalizer of that four-group. -/
theorem centralizer_three_rank_le_one_of_symmetric_four
    (hG : IsQuasithin G) (L : Subgroup G) (hZ : center L = ⊥)
    (F : Subgroup L) [IsKleinFour F]
    (eF : normalizer (F : Set L) ≃* Equiv.Perm (Fin 4)) :
    primeRank 3 (centralizer (L : Set G)) ≤ 1 := by
  let E := F.map L.subtype
  let J := (normalizer (F : Set L)).map L.subtype
  let C := centralizer (L : Set G)
  let N := normalizer (E : Set G)
  have hJL : J ≤ L := map_subtype_le _
  have hEL : E ≤ L := map_subtype_le _
  have hJN : J ≤ N := le_normalizer_map L.subtype
  have hCN : C ≤ N := (centralizer_le hEL).trans (Subgroup.centralizer_le_normalizer _)
  have hJC : J ≤ centralizer (C : Set G) := hJL.trans (le_centralizer_iff.mp le_rfl)
  have hdis : Disjoint J C := by
    apply disjoint_def.mpr
    intro x hxJ hxC
    have hxc : (⟨x,hJL hxJ⟩ : L) ∈ center L :=
      mem_center_iff.mpr (fun y => Subtype.ext (hxC y y.property))
    rw [hZ,mem_bot] at hxc
    exact congrArg Subtype.val hxc
  have hthree : 3 ∣ Nat.card J := by
    rw [Nat.card_congr ((normalizer (F : Set L)).equivMapOfInjective
      L.subtype L.subtype_injective).symm.toEquiv, Nat.card_congr eF.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  have hrJ := rank_three_pos_of_dvd hthree
  have hEcard : Nat.card E = 4 := by
    rw [card_map_of_injective L.subtype_injective]
    exact IsKleinFour.card_four
  have hE : E ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hEcard
    omega
  let : IsElementaryAbelian 2 F := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by simp }
  have hrN : primeRank 3 N ≤ 2 := isQuasithin_iff_twoLocal.mp hG N
    ⟨E,hE,(IsElementaryAbelian.isPGroup 2 F).map L.subtype,rfl⟩
    3 Nat.prime_three (by decide)
  have hr := (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion (sup_le hJN hCN))
    (inclusion_injective (sup_le hJN hCN))).trans hrN
  rw [primeRank_sup_eq_add_of_disjoint_commuting J C hdis hJC] at hr
  change primeRank 3 C ≤ 1
  omega

/-- Literal source application: a commuting cubic-rank-two overcomponent
would violate the original quasithin hypothesis. -/
theorem source_no_commuting_three_rank_two
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (X : Subgroup G) (hXC : X ≤ centralizer (K : Set G))
    (hr : 2 ≤ primeRank 3 X) : False := by
  obtain ⟨F,hF,⟨eF⟩⟩ :=
    (MathieuSourceSetup.small_remaining_component c hG hempty hgen hb).exists_symmetric_four
  let : IsKleinFour F := hF
  have hC := centralizer_three_rank_le_one_of_symmetric_four hG.quasithin K
    (MathieuSourceSetup.component_center_eq_bot c hG hempty hgen) F eF
  have hX := Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hXC) (inclusion_injective hXC)
  omega

end CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource

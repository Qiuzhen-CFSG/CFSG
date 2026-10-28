module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.ChiefCases
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Transport

/-!
# The full fourth alternative and its ambient obstruction

The local central four and natural summand are transported into the original
group. If S preserves L and fixes that four pointwise, the bound on Ω₁(Z(S))
is already enough: a nontrivial normal two-subgroup inside the natural summand
meets Z(S), contradicting the direct sum. This avoids any equality between
the Sylow subgroup of LR and S, and any assumed rank bound on the former.

The source proofs of S-normalization and pointwise fixation of the central
four remain obligations. No theorem here asserts those additional inputs.

Source: Aschbacher–Smith, C.1.34(4), printed p.136, and 15.3.23,
printed p.1128.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases

variable {D : Type*} [Group D]

/-- Every clause of C.1.34(4), specialized to the binary quotient. -/
structure FourthCase (L R : Subgroup D) (P : Sylow 2 D)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Prop where
  elementary : IsElementaryAbelian 2 (sourceFixed L)
  order : Nat.card (sourceFixed L) = 2 ^ (2 * 1)
  central : sourceFixed L ≤ center D
  fixed_le_center : sourceFixed L ≤ sourceCenter L
  natural_le_center : sourceNatural L ≤ sourceCenter L
  direct_sum : (sourceNatural L |>.subgroupOf (sourceCenter L)).IsComplement'
    (sourceFixed L |>.subgroupOf (sourceCenter L))
  natural : Nonempty (LayerModel L (sourceNatural L) ⊥ e (NaturalCopies (ZMod 2) 1))
  frattini_dual : Nonempty (LayerModel L (sourceFrattini L) (sourceCenter L) e
    (DualCopies (ZMod 2) 1))
  centralizer_dual : Nonempty (LayerModel L (sourceFrattiniCentralizer L) (sourceFrattini L) e
    (DualCopies (ZMod 2) 2))
  upper_natural : Nonempty (LayerModel L (sourceQ L) (sourceFrattiniCentralizer L) e
    (NaturalCopies (ZMod 2) 2))
  radical : RadicalInequality R P

/-- The record retains the complete alternative, including every higher layer. -/
theorem FourthCase.alternatives {L R : Subgroup D} {P : Sylow 2 D}
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (h : FourthCase L R P e) : Alternatives (ZMod 2) 1 L R P e :=
  .four h.elementary h.order h.central h.fixed_le_center h.natural_le_center
    h.direct_sum h.natural h.frattini_dual h.centralizer_dual h.upper_natural h.radical

private theorem no_disjoint_normal_layer [Finite D] (S C U : Subgroup D)
    (hS : IsPGroup 2 S)
    (hrank : primeRank 2 (Stellmacher.omegaOneCenterAmbient S) ≤ 2)
    (hC : C ≤ Stellmacher.omegaOneCenterAmbient S) (hcard : Nat.card C = 4)
    (hUS : U ≤ S) (hn : S ≤ normalizer (U : Set D))
    (hne : U ≠ ⊥) (hpow : ∀ u ∈ U, u ^ 2 = 1) (hd : Disjoint U C) : False := by
  let O := Stellmacher.omegaOneCenterAmbient S
  let : IsElementaryAbelian 2 O := Stellmacher.omegaOneCenterAmbient_elementaryAbelian S
  have hcO : Nat.card O ≤ 4 := by
    have hh := (primeRank_le_iff_elementary_card_le O).mp hrank ⊤
      (IsElementaryAbelian.of_surjective (Subgroup.topEquiv (G := O)).symm.toMonoidHom
        (Subgroup.topEquiv (G := O)).symm.surjective)
    simpa using hh
  have heq : C = O := eq_of_le_of_card_ge hC (by rw [hcard]; exact hcO)
  let N := U.subgroupOf S
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Nontrivial U := (nontrivial_iff_ne_bot _).mpr hne
  let : Nontrivial N := (subgroupOfEquivOfLe hUS).toEquiv.nontrivial
  let : Fact (IsPGroup 2 S) := ⟨hS⟩
  obtain ⟨u, hune, huZ⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  have huO : ((u : S) : D) ∈ O := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff S _).mpr
    refine ⟨(u : S).property, hpow _ u.property, ?_⟩
    intro s hs
    exact congrArg Subtype.val (mem_center_iff.mp huZ ⟨s, hs⟩)
  have huC : ((u : S) : D) ∈ C := heq.symm ▸ huO
  have hu1 : ((u : S) : D) = 1 := hd.le_bot ⟨u.property, huC⟩
  exact hune (Subtype.ext (Subtype.ext hu1))

variable {G : Type*} [Group G] [Finite G]

/-- An ambient comparison suffices; no local Sylow rank or equality is assumed.
The two additional ambient action hypotheses still require source proofs. -/
theorem fourthCase_impossible_of_ambient_action (d : LocalData G)
    {L H : Subgroup G} (hLH : L ≤ H) (hcomp : (L.subgroupOf H).IsCComponent)
    (R : Subgroup H) (P : Sylow 2 H)
    (e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hfour : FourthCase (L.subgroupOf H) R P e)
    (hcore : L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4)
    (hSL : d.S ≤ normalizer (L : Set G))
    (hSC : d.S ≤ centralizer (coreFixed L : Set G)) : False := by
  have hQS : commutatorCore L ≤ d.S := commutatorCore_le_S d L hcore hR
  have hZS' : coreCenter L ≤ d.S := (map_subtype_le _).trans hQS
  have hUS : coreNatural L ≤ d.S := by
    rw [← sourceNatural_map hLH hcomp]
    exact (map_mono hfour.natural_le_center).trans
      ((sourceCenter_map_subtype hLH hcomp).le.trans hZS')
  have hCS : coreFixed L ≤ d.S := inf_le_left.trans hQS
  have helem : IsElementaryAbelian 2 (coreFixed L) := by
    rw [← sourceFixed_map hLH hcomp]
    exact hfour.elementary.map H.subtype
  let _ := helem
  have hc : Nat.card (coreFixed L) = 4 := by
    rw [← sourceFixed_map hLH hcomp, card_map_of_injective H.subtype_injective]
    exact hfour.order
  have hC : coreFixed L ≤ Stellmacher.omegaOneCenterAmbient d.S := by
    intro x hx
    refine (Stellmacher.mem_omegaOneCenterAmbient_iff d.S x).mpr
      ⟨hCS hx, elemPow_eq_one_of_isElementaryAbelian x hx, ?_⟩
    intro s hs
    exact (hSC hs x hx).symm
  have hm : Nonempty (LayerModel L (coreNatural L) ⊥ (ambientMarking hLH e)
      (NaturalCopies (ZMod 2) 1)) := by
    obtain ⟨m⟩ := hfour.natural
    have h := ambientLayer hLH m
    rw [sourceNatural_map hLH hcomp, Subgroup.map_bot] at h
    exact ⟨h⟩
  obtain ⟨m⟩ := hm
  have horder : Nat.card (coreNatural L) = 8 := by
    rw [Nat.card_congr m.upperIso.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hne : coreNatural L ≠ ⊥ := by
    intro h
    rw [h] at horder
    norm_num at horder
  have hpow : ∀ u ∈ coreNatural L, u ^ 2 = 1 := by
    intro u hu
    have hh : (⟨u, hu⟩ : coreNatural L) ^ 2 = 1 := by
      apply m.upperIso.injective
      rw [map_pow, map_one]
      change (2 : ℕ) • (Multiplicative.toAdd (m.upperIso ⟨u, hu⟩)) = 0
      ext i j
      simp only [Pi.smul_apply, Pi.zero_apply]
      exact CharTwo.two_nsmul _
    exact congrArg Subtype.val hh
  have hd : Disjoint (coreNatural L) (coreFixed L) := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    rintro x ⟨hu, hc⟩
    rw [← sourceNatural_map hLH hcomp] at hu
    rw [← sourceFixed_map hLH hcomp] at hc
    obtain ⟨u, hu, rfl⟩ := hu
    obtain ⟨v, hv, he⟩ := hc
    have huv : v = u := Subtype.ext he
    have hc' : u ∈ sourceFixed (L.subgroupOf H) := huv ▸ hv
    have hmem : (⟨u, hfour.natural_le_center hu⟩ : sourceCenter (L.subgroupOf H)) ∈
        (sourceNatural (L.subgroupOf H)).subgroupOf (sourceCenter (L.subgroupOf H)) ⊓
          (sourceFixed (L.subgroupOf H)).subgroupOf (sourceCenter (L.subgroupOf H)) := ⟨hu, hc'⟩
    have hu1 := hfour.direct_sum.disjoint.le_bot hmem
    exact congrArg (fun z : sourceCenter (L.subgroupOf H) => ((z : H) : G))
      (show (⟨u, hfour.natural_le_center hu⟩ : sourceCenter (L.subgroupOf H)) = 1 from hu1)
  exact no_disjoint_normal_layer d.S (coreFixed L) (coreNatural L)
    (d.T.isPGroup'.to_le inf_le_left) (centralOmega_rank_le_two d hindex hZ hZS)
    hC hc hUS (coreNatural_normalized d.S hSL) hne hpow hd

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases
end

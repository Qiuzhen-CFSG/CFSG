module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Core
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Projection
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Stellmacher.OmegaOneCenterMap

/-!
# Excluding the six-chief-factor alternative

In C.1.34(4), the central elementary four-group C_Q(L) exhausts the
central omega subgroup if its rank is at most two. The nontrivial natural
summand U is normal in the local Sylow two-group, so it contains a nonidentity
central involution. That involution lies in C_Q(L), contradicting the direct
sum in Z(Q). The proof uses the actual natural-layer isomorphism to establish
nontriviality and exponent two; no numerical chief-factor tag is used.

The reduction retains every clause and the common action marking of cases
(1), (2), (3), and (5). Its rank premise is intrinsic to the local Sylow group.
The application to 15.3.23 must transport the source Sylow arrangement before
using the bound from 15.3.8; that arrangement is not asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.34(4), printed p.136, and 15.3.23, printed p.1128.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

variable {D : Type*} [Group D] [Finite D]

private theorem no_disjoint_normal_layer (S C U : Subgroup D)
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

/-- The central four and its disjoint natural summand exclude C.1.34(4). -/
theorem caseFour_impossible (L : Subgroup D) [L.Normal] (S : Sylow 2 D)
    (hrank : primeRank 2 (Stellmacher.omegaOneCenterAmbient (S : Subgroup D)) ≤ 2)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (helem : IsElementaryAbelian 2 (sourceFixed L))
    (hcard : Nat.card (sourceFixed L) = 2 ^ (2 * 1))
    (hcentral : sourceFixed L ≤ center D)
    (hCZ : sourceFixed L ≤ sourceCenter L)
    (hUZ : sourceNatural L ≤ sourceCenter L)
    (hs : (sourceNatural L |>.subgroupOf (sourceCenter L)).IsComplement'
      (sourceFixed L |>.subgroupOf (sourceCenter L)))
    (m : LayerModel L (sourceNatural L) ⊥ e (NaturalCopies (ZMod 2) 1)) : False := by
  let := helem
  have hQS : sourceQ L ≤ (S : Subgroup D) :=
    (commutator_le_left _ _).trans (pCore_isPGroup.le_sylow_of_normal S)
  have hZS : sourceCenter L ≤ (S : Subgroup D) := (map_subtype_le _).trans hQS
  have hUS := hUZ.trans hZS
  have hCS := hCZ.trans hZS
  have hC : sourceFixed L ≤ Stellmacher.omegaOneCenterAmbient (S : Subgroup D) := by
    intro c hc
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hCS hc, elemPow_eq_one_of_isElementaryAbelian c hc,
        fun s _ => mem_center_iff.mp (hcentral hc) s⟩
  let hQn : (sourceQ L).Normal := inferInstance
  have hZn : (sourceCenter L).Normal :=
    inferInstanceAs ((center (sourceQ L)).map (sourceQ L).subtype).Normal
  let := hZn
  have hUn : (sourceNatural L).Normal := inferInstanceAs (⁅sourceCenter L, L⁆).Normal
  have hn : (S : Subgroup D) ≤ normalizer (sourceNatural L : Set D) := by
    let := hUn
    rw [normalizer_eq_top]
    exact le_top
  have horder : Nat.card (sourceNatural L) = 8 := by
    rw [Nat.card_congr m.upperIso.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hne : sourceNatural L ≠ ⊥ := by
    intro h
    rw [h] at horder
    norm_num at horder
  have hpow : ∀ u ∈ sourceNatural L, u ^ 2 = 1 := by
    intro u hu
    have hh : (⟨u, hu⟩ : sourceNatural L) ^ 2 = 1 := by
      apply m.upperIso.injective
      rw [map_pow, map_one]
      change (2 : ℕ) • (Multiplicative.toAdd (m.upperIso ⟨u, hu⟩)) = 0
      ext i j
      simp only [Pi.smul_apply, Pi.zero_apply]
      exact CharTwo.two_nsmul _
    exact congrArg Subtype.val hh
  have hd : Disjoint (sourceNatural L) (sourceFixed L) := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro u hu
    have hmem : (⟨u, hUZ hu.1⟩ : sourceCenter L) ∈
        (sourceNatural L).subgroupOf (sourceCenter L) ⊓
          (sourceFixed L).subgroupOf (sourceCenter L) := hu
    exact congrArg Subtype.val (show (⟨u, hUZ hu.1⟩ : sourceCenter L) = 1 from
      hs.disjoint.le_bot hmem)
  exact no_disjoint_normal_layer (S : Subgroup D) (sourceFixed L)
    (sourceNatural L) S.isPGroup' hrank hC (by simpa using hcard) hUS hn hne hpow hd

/-- The three full alternatives needed by the subsequent core-action argument.
Every layer uses the same actual quotient marking, including the dual layers. -/
inductive FirstThreeCases (L R : Subgroup D) (S : Sylow 2 D)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Prop
  | one (block : CFSG.Quasithin.ChapterC.IsSL3EvenBlock L 1)
      (natural : Nonempty (LayerModel L (sourceQ L) ⊥ e (NaturalCopies (ZMod 2) 1)))
  | two (natural : Nonempty (LayerModel L (sourceQ L) ⊥ e (NaturalCopies (ZMod 2) 2)))
      (radical : RadicalInequality R S)
  | three (natural : Nonempty (LayerModel L (sourceCenter L) ⊥ e (NaturalCopies (ZMod 2) 1)))
      (dual : Nonempty (LayerModel L (sourceQ L) (sourceCenter L) e (DualCopies (ZMod 2) 2)))
      (radical : RadicalInequality R S)

/-- All of case (5), retained until the actual invariant-line obstruction is proved. -/
structure FifthCase (L R : Subgroup D) (S : Sylow 2 D)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Prop where
  binary_quotient : Nonempty ((L ⧸ pCore 2 L) ≃*
    CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.Natural.Actor)
  fixed_order : Nat.card (sourceFixed L) = 2
  natural : Nonempty (LayerModel L (sourceQ L) (sourceFixed L) e (NaturalCopies (ZMod 2) 1))
  central_omega : Stellmacher.omegaOneCenterAmbient (S : Subgroup D) ≤ center D
  radical : IndexSevenPointRadical L R S

/-- Remove case (4) from the complete five-case theorem, preserving all other clauses. -/
theorem alternatives_without_four {L R : Subgroup D} [L.Normal]
    (S : Sylow 2 D)
    (hrank : primeRank 2 (Stellmacher.omegaOneCenterAmbient (S : Subgroup D)) ≤ 2)
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (h : Alternatives (ZMod 2) 1 L R S e) :
    FirstThreeCases L R S e ∨ FifthCase L R S e := by
  cases h with
  | one hb hn => exact Or.inl (.one hb hn)
  | two hn hr => exact Or.inl (.two hn hr)
  | three hn hd hr => exact Or.inl (.three hn hd hr)
  | four he hc hz hCZ hUZ hs hn _ _ _ _ =>
    obtain ⟨m⟩ := hn
    exact (caseFour_impossible L S hrank e he hc hz hCZ hUZ hs m).elim
  | five hb hc hn hz hr => exact Or.inr ⟨hb, hc, hn, hz, hr⟩

/-- Transport 15.3.8 through an actual local Sylow embedding. Equality of
the embedded Sylow subgroup with S must be established by the application. -/
theorem local_centralOmega_rank_le_two (d : LocalData D) (H : Subgroup D)
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = d.S)
    (hindex : (d.S.subgroupOf (d.T : Subgroup D)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4) :
    primeRank 2 (Stellmacher.omegaOneCenterAmbient (P : Subgroup H)) ≤ 2 := by
  have hmap : (Stellmacher.omegaOneCenterAmbient (P : Subgroup H)).map H.subtype =
      centralOmegaIn d.S := by
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      hP]
    rfl
  have hr := Theory.GroupTheory.primeRank_equiv 2 (equivMapOfInjective
    (Stellmacher.omegaOneCenterAmbient (P : Subgroup H)) H.subtype H.subtype_injective)
  rw [hmap] at hr
  exact hr.le.trans (centralOmega_rank_le_two d hindex hZ hZS)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree

end

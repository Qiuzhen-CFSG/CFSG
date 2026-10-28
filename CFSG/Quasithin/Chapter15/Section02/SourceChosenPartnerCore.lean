module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Definitions
public import CFSG.Quasithin.Chapter15.Section01.CentralizingControl
public import Theory.PPrimeCore
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The residual-core reduction and last parabolic contradiction in 15.2.27

Every three-free subgroup of Mc containing T lies in M: finite minimal
selection would otherwise produce an H-star member, whose S₃-wreath
quotient has order divisible by three. Applying this to O₃′(Mc)T gives
the opening claim of the printed proof of 15.2.27(1).

If V is outside O₂(Mc), its order sixteen and the nontrivial central seed
bound |(V ∩ O₂(Mc))/Z| by four. Equality forces |Z| and |V:V ∩ O₂(Mc)|
to be two. This is only the numerical input to chief-action recognition;
it does not claim that the whole action on O₂(Mc)/Z is irreducible.

The final parabolic argument uses the prepared residual-centralization
input on M ∩ C_G(Z). A minimal moving parabolic outside M is an H-star
member and contradicts the common-plane conclusion of 15.2.11(2) and
15.2.13; one inside M contradicts that prepared input instead.

Full 15.2.27(2) still requires the generalized-Fitting reduction, the
faithful chief-action classification, and construction of this parabolic.
Neither its existence nor partner-core containment is assumed as an
earlier source fact. No result from 15.2.26 or weak closure is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.27, printed pp.1118--1119, refs/quasithin.pdf pp.1135--1136.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

private theorem wreath_three_dvd {D : Type*} [Group D] [Finite D]
    (he : Nonempty ((D ⧸ pCore 2 D) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    3 ∣ Nat.card D := by
  obtain ⟨e⟩ := he
  have hc : Nat.card (D ⧸ pCore 2 D) = 72 := by
    rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card]
  exact (show 3 ∣ Nat.card (D ⧸ pCore 2 D) by rw [hc]; norm_num).trans
    (card_quotient_dvd_card _)

/-- Every three-free subgroup of Mc containing T lies in M. -/
theorem source_chosen_threeFree_overgroup_le
    {T : Sylow 2 G} {M Mc V X : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hTX : (T : Subgroup G) ≤ X) (hXMc : X ≤ Mc)
    (hcop : Nat.Coprime 3 (Nat.card X)) : X ≤ M := by
  classical
  by_contra hn
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton _
  have hX : X ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTX hXMc
      ⟨Chapter1.mem_H_of_isTwoLocal hMc.1.1, hTX.trans hXMc⟩
  let S : Set (Subgroup G) := {P | P ∈ Chapter1.HOver G (T : Set G) ∧ ¬ P ≤ M ∧ P ≤ X}
  obtain ⟨P, hP⟩ := (Set.toFinite S).exists_minimalFor id S ⟨X, hX, hn, le_rfl⟩
  have hpstar : P ∈ Chapter3.HStar (T : Subgroup G) M := by
    refine ⟨⟨hP.1.1, hP.1.2.1⟩, ?_⟩
    intro Q hQ hQP
    exact hP.2 ⟨hQ.1, hQ.2, hQP.trans hP.1.2.2⟩ hQP
  have hdiv : 3 ∣ Nat.card X :=
    (wreath_three_dvd (hquotient P hpstar)).trans (card_dvd_of_le hP.1.2.2)
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop) hdiv

/-- The first claim in the proof of 15.2.27(1). -/
theorem source_chosen_threePrimeCore_le
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    (pPrimeCore 3 Mc).map Mc.subtype ≤ M ⊓ Mc := by
  let N := (pPrimeCore 3 Mc).map Mc.subtype
  have hTMc : (T : Subgroup G) ≤ Mc := hg.outside.1.1.2.trans hg.in_partner
  have hNMc : N ≤ Mc := map_subtype_le _
  have hMcN : Mc ≤ normalizer (N : Set G) := by
    simpa only [N, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pPrimeCore 3 Mc).le_normalizer_map Mc.subtype
  have hNcop : Nat.Coprime 3 (Nat.card N) :=
    (pPrimeCore_coprime_card (p := 3) (G := Mc)).of_dvd_right (card_map_dvd _ _)
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hTcop : Nat.Coprime 3 (Nat.card (T : Subgroup G)) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes N (T : Subgroup G)
    (hTMc.trans hMcN)
  have hcop : Nat.Coprime 3 (Nat.card (N ⊔ (T : Subgroup G) : Subgroup G)) :=
    (hNcop.mul_right hTcop).of_dvd_right ⟨Nat.card (N ⊓ (T : Subgroup G) : Subgroup G),
      hcard.trans (Nat.mul_comm _ _)⟩
  exact le_inf (le_sup_left.trans (source_chosen_threeFree_overgroup_le h hquotient
    le_sup_right (sup_le hNMc hTMc) hcop)) hNMc

/-- A possible last parabolic in the noncore argument. This records its
literal position, minimality, and movement, not its existence. -/
structure ChosenMovingParabolic (T : Sylow 2 G) (M Mc ZS P : Subgroup G) : Prop where
  sylow_le : (T : Subgroup G) ≤ P
  in_partner : P ≤ Mc
  proper : ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Y < P → Y ≤ M
  moves : ¬ residual P ≤ centralizer (ZS : Set G)

/-- The prepared residual input centralizes the plane on every subgroup
of the literal intersection M ∩ Mc. -/
theorem source_chosen_intersection_residual_centralizes_plane
    {T : Sylow 2 G} {M Mc V H ZS P : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hPM : P ≤ M) (hPMc : P ≤ Mc) :
    residual P ≤ centralizer (ZS : Set G) := by
  have hP : P ≤ M ⊓ centralizer (centralInvolutions T : Set G) :=
    le_inf hPM (hPMc.trans_eq hMc)
  exact (embedded_pResidual_mono 2 hP).trans
    (h.prepared.seed_residual.trans (centralizer_le hg.plane_le))

/-- The final parabolic contradiction of 15.2.27, with the preceding
15.2.11(2)/15.2.13 common-plane conclusion explicit. -/
theorem source_chosen_moving_parabolic_false
    {T : Sylow 2 G} {M Mc V H ZS P : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G))
    (hp : ChosenMovingParabolic T M Mc ZS P) : False := by
  by_cases hPM : P ≤ M
  · exact hp.moves (source_chosen_intersection_residual_centralizes_plane h hg hMc
      hPM hp.in_partner)
  · have hMcH : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton _
    have hPH : P ∈ Chapter1.HOver G (T : Set G) :=
      Chapter3.mem_HOver_of_sylow_interval T hp.sylow_le hp.in_partner
        ⟨Chapter1.mem_H_of_isTwoLocal hMcH.1.1, hp.sylow_le.trans hp.in_partner⟩
    have hstar : P ∈ Chapter3.HStar (T : Subgroup G) M := by
      refine ⟨⟨hPH, hPM⟩, ?_⟩
      intro Y hY hYP
      by_contra hn
      exact hY.2 (hp.proper Y hY.1.2 (lt_of_le_not_ge hYP hn))
    exact hp.moves (hplane P hstar)

/-- The seed lies in the partner two-core, using its actual centralizer
identification, not a conclusion about V. -/
theorem source_chosen_seed_le_partner_core
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) :
    centralInvolutions T ≤ V ⊓ twoCoreIn Mc := by
  let := h.prepared.elementary
  have hZV := hZ.trans hg.plane_le
  have hZMc := hZV.trans ((h.prepared.inside_core H hg.outside).trans
    ((twoCore_le H).trans hg.in_partner))
  have hZp : IsPGroup 2 (centralInvolutions T) :=
    (IsElementaryAbelian.isPGroup 2 V).to_le hZV
  have hnorm : Mc ≤ normalizer (centralInvolutions T : Set G) := by
    rw [hMc]
    exact Subgroup.centralizer_le_normalizer _
  exact le_inf hZV (le_pCoreIn_of_normalizes hZp hZMc hnorm)

/-- The size calculation before the faithful-chief-action step of 15.2.27.
Equality forces both the seed and the nontrivial core image of V to have
order two. No assertion of faithfulness on Qc/Z is made here. -/
theorem source_chosen_noncore_section_bound
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) (hn : ¬ V ≤ twoCoreIn Mc) :
    (centralInvolutions T).relIndex (V ⊓ twoCoreIn Mc) ≤ 4 ∧
      ((centralInvolutions T).relIndex (V ⊓ twoCoreIn Mc) = 4 →
        Nat.card (centralInvolutions T) = 2 ∧ (V ⊓ twoCoreIn Mc).relIndex V = 2) := by
  have hZC := source_chosen_seed_le_partner_core h hg hMc hZ
  have hseed : 2 ≤ Nat.card (centralInvolutions T) := by
    have hh := (one_lt_card_iff_ne_bot (H := centralInvolutions T)).mpr
      (Section03.InitialSource.centralInvolutions_ne_bot_of_maximal_local T h.maximal.1)
    omega
  have hindex : 2 ≤ (V ⊓ twoCoreIn Mc).relIndex V := by
    have hpos : (V ⊓ twoCoreIn Mc).relIndex V ≠ 0 :=
      ((V ⊓ twoCoreIn Mc).subgroupOf V).index_ne_zero_of_finite
    have hne : (V ⊓ twoCoreIn Mc).relIndex V ≠ 1 := by
      intro he
      exact hn ((relIndex_eq_one.mp he).trans inf_le_right)
    omega
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup G)
    (centralInvolutions T) (V ⊓ twoCoreIn Mc) bot_le hZC
  rw [relIndex_bot_left, relIndex_bot_left] at hprod
  have hprodV := relIndex_mul_relIndex (⊥ : Subgroup G)
    (V ⊓ twoCoreIn Mc) V bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, h.card_eq_sixteen] at hprodV
  have hsmall : Nat.card (V ⊓ twoCoreIn Mc : Subgroup G) ≤ 8 := by nlinarith
  have hpos : 0 < (centralInvolutions T).relIndex (V ⊓ twoCoreIn Mc) :=
    Nat.pos_of_ne_zero ((centralInvolutions T).subgroupOf (V ⊓ twoCoreIn Mc)).index_ne_zero_of_finite
  constructor
  · nlinarith
  · intro he
    rw [he] at hprod
    constructor <;> nlinarith

end CFSG.Quasithin.Chapter15.Section02


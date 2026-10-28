module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNinePartner

/-!
# Sylow normalization of the original marked centralizers

Let E have order four and let D centralize a nontrivial subgroup U of E.
For every Z1 <= E, its centralizer in D is either D or C_D(E): if Z1 is
not contained in U, their join is E. Hence any subgroup normalizing both
E and D normalizes C_D(Z1). This requires no normalization of E by D.

The full Nine source identifies Mc with C_G(Z). Its Thompson fixed plane
contains the original nontrivial Z and is normalized by T, so every marked
centralizer C_Mc(Z1) is T-invariant independently of original 15.1.14(1).

Source: Aschbacher--Smith 15.1.13--18, printed pp.1090--1093.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem sup_eq_four_of_nontrivial_and_not_le
    (E U A : Subgroup G) (hE : Nat.card E = 4)
    (hUE : U ≤ E) (hU : U ≠ ⊥) (hAE : A ≤ E) (hAU : ¬ A ≤ U) :
    U ⊔ A = E := by
  let K := U ⊔ A
  have hKE : K ≤ E := sup_le hUE hAE
  have hlow := (one_lt_card_iff_ne_bot U).mpr hU
  have hUK : U < K := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hAU (he.symm ▸ le_sup_right))
  have hlarge : 2 < Nat.card K := by
    by_contra hn
    have he : U = K := eq_of_le_of_card_ge hUK.le (by omega)
    exact hUK.ne he
  have hd : Nat.card K ∣ 4 := hE ▸ card_dvd_of_le hKE
  have hle : Nat.card K ≤ 4 := (card_le_of_le hKE).trans_eq hE
  have hne3 : Nat.card K ≠ 3 := by
    intro he
    rw [he] at hd
    norm_num at hd
  have hcard : Nat.card E ≤ Nat.card K := by
    rw [hE]
    omega
  exact eq_of_le_of_card_ge hKE hcard

/-- In the centralizer of a nontrivial subgroup of a four-group, every
marked centralizer is either the whole group or the whole four-group's centralizer. -/
theorem marked_centralizer_alternatives_of_four
    (D E U Z1 : Subgroup G) (hE : Nat.card E = 4)
    (hUE : U ≤ E) (hU : U ≠ ⊥) (hDU : D ≤ centralizer (U : Set G))
    (hZ : Z1 ≤ E) :
    D ⊓ centralizer (Z1 : Set G) = D ∨
      D ⊓ centralizer (Z1 : Set G) = D ⊓ centralizer (E : Set G) := by
  by_cases hZU : Z1 ≤ U
  · exact Or.inl (inf_eq_left.mpr (hDU.trans (centralizer_le hZU)))
  · right
    have he := sup_eq_four_of_nontrivial_and_not_le E U Z1 hE hUE hU hZ hZU
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      apply le_centralizer_iff.mpr
      rw [←he]
      exact sup_le
        (le_centralizer_iff.mp (inf_le_left.trans hDU))
        (le_centralizer_iff.mp inf_le_right)
    · exact inf_le_inf_left D (centralizer_le hZ)

/-- Normalizing D and its marked four-group suffices to normalize every
marked centralizer, without requiring D to normalize the four-group. -/
theorem normalizes_marked_centralizer_of_four
    (T D E U Z1 : Subgroup G) (hE : Nat.card E = 4)
    (hUE : U ≤ E) (hU : U ≠ ⊥) (hDU : D ≤ centralizer (U : Set G))
    (hZ : Z1 ≤ E) (hTE : T ≤ normalizer (E : Set G))
    (hTD : T ≤ normalizer (D : Set G)) :
    T ≤ normalizer (D ⊓ centralizer (Z1 : Set G) : Set G) := by
  change T ≤ normalizer ((D ⊓ centralizer (Z1 : Set G) : Subgroup G) : Set G)
  rcases marked_centralizer_alternatives_of_four D E U Z1 hE hUE hU hDU hZ with he | he
  · rwa [he]
  · rw [he]
    exact (le_inf hTD (hTE.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf

/-- Every marked subgroup of the original full Nine fixed plane has a
T-invariant partner centralizer, independently of global residual centralization. -/
theorem PreparedChosenModule.nine_marked_partner_centralizer_normalized
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hstrict : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict <
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)
    (hZ : Z1 ≤ thompsonFixed T V) :
    (T : Subgroup G) ≤ normalizer (Mc ⊓ centralizer (Z1 : Set G) : Set G) := by
  have hMc := (h.nine_partner_centralizer hG T hempty hM hJ hu hne hfull h9).1
  have hfour := (h.nine_fixed_card_of_strict_thompson_image
    hG T hempty hM hmany hJ h9 hstrict).2
  have hZE : centralInvolutions T ≤ thompsonFixed T V := by
    refine le_inf ?_ ?_
    · rw [hfull]
      exact le_conjugateSpanBy _ _
    · intro z hz j hj
      exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 j
        (ChapterB.thompsonJ_le _ _ hj)
  have hTE : (T : Subgroup G) ≤ normalizer (thompsonFixed T V : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMc]
    exact le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)
  exact normalizes_marked_centralizer_of_four (T : Subgroup G) Mc
    (thompsonFixed T V) (centralInvolutions T) Z1 hfour hZE
    (centralInvolutions_ne_bot_of_maximal_local T hM.1) hMc.le hZ hTE
    (hTMc.trans Mc.le_normalizer)

end CFSG.Quasithin.Chapter15.Section01

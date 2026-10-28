module
public import CFSG.Quasithin.Chapter14.Section06.SourceF9
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.PrimeByTwo
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.OriginalF916

/-!
# The actual quadratic bound in the abelian plane branch

The source plane equals its distinguished seed, so an element centralizing
that seed already centralizes the whole plane. The original F.9.16 proof
therefore applies with its centralizer alternative discharged immediately.
Original rank-two transitivity and abelian closure supply commuting
intersecting conjugates. The output keeps the literal H/O₂(H) action on
⟨Vᴴ⟩/Z, and its prime-by-two application gives p = 3 or 5 without an assumed
quadratic bound or actor.

Source: Aschbacher--Smith, 14.5.18(3), 14.6.12(1), printed pp.1018,1031;
F.9.16(3), printed p.324. The prime-by-two hypothesis is supplied by the
solvable minimal-parabolic reduction in SourceOddCoreReduction.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.ModuleBound
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

theorem source_rankTwo_intersecting_conjugates_commute (g : G)
    (hi : localModule T M ⊓ (localModule T M).map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅localModule T M,(localModule T M).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let h := Section02.source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨he,F,hp,_,_,_⟩ := Section02.source_lemma_14_2_6 hG T hempty hM hu hmany hcard e
  let := he
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFH : F.H = Mc := by
    change normalizer (F.Vi 1 : Set G) = Mc
    rw [hp,hMc]
    exact le_antisymm (normalizer_le_centralizer_of_card_two _
      (plane_centralInvolutions_card T M hM.1.2 hcard e)) (Subgroup.centralizer_le_normalizer _)
  have habF : IsMulCommutative F.U := by
    change IsMulCommutative (conjugateSpanBy (rankTwoSeed T M) F.H)
    rw [hFH,Section02.rankTwoSeed_eq_localModule]
    exact hab
  have hc := (h.abelian_U_iff_intersections_commute F).mp habF g⁻¹
  simpa only [Section02.rankTwoSeed_eq_localModule,conjugate,inv_inv] using hc (by simpa only [Section02.rankTwoSeed_eq_localModule,conjugate,inv_inv] using hi)

theorem source_rankTwo_quadratic_bound
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H),
      let := hU
      ∃ a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T),
        quadraticRatio a.representation ≤ 2 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH
  let : IsElementaryAbelian 2 (localModule T M) := h.elementary
  let : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H) :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  apply OriginalF916.original_bounded_action (SourceF91.ofF91 h)
  · exact source_rankTwo_intersecting_conjugates_commute hG T hempty hM hu hmany hcard e hab
  · intro x hx
    left
    rw [commutator_eq_bot_iff_le_centralizer,le_centralizer_iff]
    exact zpowers_le.mpr hx


theorem source_rankTwo_odd_prime_restriction
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ pCore p (H ⧸ pCore 2 H))) :
    p = 3 ∨ p = 5 := by
  obtain ⟨hU,a,ha⟩ := source_rankTwo_quadratic_bound
    hG T hempty hM hu hmany hcard e hab H hH
  let := hU
  exact ChapterD.prime_restriction_of_prime_by_two a.representation a.faithful ho
    (pCore_quotient_pCore_eq_bot 2) hq ((cubicRatio_le_quadraticRatio _).trans ha)

end CFSG.Quasithin.Chapter14.Section06

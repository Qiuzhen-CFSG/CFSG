module
public import CFSG.Quasithin.Chapter15.Section01.OrderingSource.ActionPlacement
public import CFSG.Quasithin.Chapter15.Section01.OrderingSource.ThompsonOdd

/-!
# The source uniqueness and span conclusions of 14.1.4

If J(T) centralizes the module of an ordering-maximal local subgroup M,
Baumann control places both N_G(T) and N_G(J(T)) in M. For any other
maximal local N, the actual J(N)T action has odd two-residual. Every minimal
parabolic in this interval therefore lies in M or is covered by T and the
module centralizer. McBride's finite-lattice generation and Thompson
Frattini generation give N = (N ∩ M) C_N(V(N)). This proves the ordering
relation for every N and hence uniqueness of M as an ordering-maximal
member. The final theorem applies A.5.6 to the original conjugate span of
any nontrivial Sylow-central seed across N ∩ M.

All action images, reduced modules and odd-by-two witnesses are constructed
from the original source hypotheses by the imported source lemmas.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, original
14.1.4, printed p.976, and A.5.6, printed pp.61–62.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- Every maximal local lies below the selected centralizing maximal local in the source ordering. -/
theorem source_ordering_of_centralizing_orderingMaximal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    ∀ N ∈ maximalLocals T, OrderingLE T N M := by
  intro N hN
  by_cases hJN : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T N : Set G)
  · exact source_centralizing_local_ordering hG T hM hJ hN hJN
  have hNH : N ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
  let S := T.subtype hN.2
  let Y := elementaryAbelianMaxJ (⊤ : Subgroup N) ⊔ (S : Subgroup N)
  let D := Y.map N.subtype
  let q := localActionMap (centralInvolutions T) N
  let X := (N ⊓ M) ⊔ (N ⊓ centralizer (localModule T N : Set G))
  have hDN : D ≤ N := map_subtype_le _
  have hTD : (T : Subgroup G) ≤ D := by
    have hm := map_mono (f := N.subtype)
      (show (S : Subgroup N) ≤ Y from le_sup_right)
    change ((T : Subgroup G).subgroupOf N).map N.subtype ≤ D at hm
    rwa [map_subgroupOf_eq_of_le hN.2] at hm
  have hTX : (T : Subgroup G) ≤ X := (le_inf hN.2 hM.1.2).trans le_sup_left
  have hc := source_centralizing_baumann_control hG T hM hJ
  have hNT : normalizer (T : Set G) ≤ M := hc.2.2.2.2.2.2
  have hNJ : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M :=
    hc.2.2.2.2.2.1
  have hDodd : Odd (Nat.card (pResidual 2 (Y.map q))) :=
    source_thompsonSylow_action_oddResidual hG T hempty hNH hJN
  have hDX : D ≤ X := by
    by_cases he : D = (T : Subgroup G)
    · exact he ▸ hTX
    have hlt : (T : Subgroup G) < D := lt_of_le_of_ne hTD (Ne.symm he)
    apply (Order.eq_sSup_hasUniqueMaximalOver hlt).le.trans
    apply sSup_le
    rintro H ⟨hHD,hHP⟩
    have hHN : H ≤ N := hHD.trans hDN
    by_cases hn : H ≤ normalizer (T : Set G)
    · exact (le_inf hHN (hn.trans hNT)).trans le_sup_left
    have hHY : H.subgroupOf N ≤ Y := by
      rw [← comap_map_eq_self_of_injective N.subtype_injective Y]
      exact comap_mono hHD
    have hR : (H.subgroupOf N).map q ≤ Y.map q := map_mono hHY
    have hodd : Odd (Nat.card (pResidual 2 ((H.subgroupOf N).map q))) := by
      apply hDodd.of_dvd_nat
      rw [← card_map_of_injective (K := pResidual 2 ((H.subgroupOf N).map q))
        (inclusion_injective hR)]
      exact card_dvd_of_le (map_pResidual_le 2 (inclusion hR))
    exact source_minimalParabolic_ordering_piece hG T hempty hM hJ hNH
      ⟨hHP,hn⟩ hHN hodd
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup N)).map N.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective]
    exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le hN.2)
  have hnormalizer : (normalizer (elementaryAbelianMaxJ (S : Subgroup N) : Set N)).map
      N.subtype ≤ X := by
    have hh := (elementaryAbelianMaxJ (S : Subgroup N)).le_normalizer_map N.subtype
    rw [hJmap] at hh
    exact (le_inf (map_subtype_le _) (hh.trans hNJ)).trans le_sup_left
  have hI : (elementaryAbelianMaxJ (⊤ : Subgroup N)).map N.subtype ≤ X :=
    (map_mono (show elementaryAbelianMaxJ (⊤ : Subgroup N) ≤ Y from le_sup_left)).trans hDX
  have hNX : N ≤ X := by
    have hm := congrArg (map N.subtype) (elementaryAbelianMaxJ_frattini S)
    rw [Subgroup.map_sup,← MonoidHom.range_eq_map,range_subtype] at hm
    exact hm ▸ sup_le hnormalizer hI
  have hnC : N ≤ normalizer (N ⊓ centralizer (localModule T N : Set G) : Set G) :=
    (le_inf N.le_normalizer ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  intro x hx
  have hm := hNX hx
  have hp := coe_mul_of_left_le_normalizer_right (N ⊓ M)
    (N ⊓ centralizer (localModule T N : Set G)) (inf_le_left.trans hnC)
  change x ∈ ((N ⊓ M) ⊔ (N ⊓ centralizer (localModule T N : Set G))) at hm
  rw [show x ∈ ((N ⊓ M) ⊔ (N ⊓ centralizer (localModule T N : Set G))) ↔
      x ∈ ((N ⊓ M : Subgroup G) : Set G) *
        ((N ⊓ centralizer (localModule T N : Set G) : Subgroup G) : Set G) from
      Iff.of_eq (congrArg (fun Z : Set G => x ∈ Z) hp)] at hm
  exact hm

/-- The actual uniqueness conclusion of original 14.1.4. -/
theorem source_unique_orderingMaximal_of_centralizing
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    ∀ N, IsOrderingMaximal T N → N = M := by
  intro N hN
  exact (hN.2 M hM.1
    (source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN.1)).symm

/-- The original source hypotheses exclude every such M-invariant intersection span. -/
theorem source_no_invariant_span_of_centralizing_orderingMaximal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hN : N ∈ maximalLocals T) (hne : N ≠ M)
    (W : Subgroup G) (hW : W ≠ ⊥) (hWZ : W ≤ centralInvolutions T) :
    ¬ M ≤ normalizer (conjugateSpanBy W (N ⊓ M) : Set G) :=
  source_no_invariant_span_of_ordering hG T hM.1 hN hne
    (source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN) W hW hWZ

end CFSG.Quasithin.Chapter15.Section01

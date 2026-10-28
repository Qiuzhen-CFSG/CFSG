module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Component
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Unitary
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Selection
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Span

/-!
# Ambient reciprocity for the actual odd fixed residual

Failure of uniqueness selects the full original witnesses, including the
Sylow/core normalization. Assuming contained generalized Fitting then gives
the reversed C.2.3 setup, identifies the residual with L, promotes it to a
C-component of H, proves index two, and identifies N_G(〈L^H〉) with H.

In the unitary row the proved odd-rank obstruction forces this component to
be normal, contradicting the index. This proves the full required escape
for that row. The Suzuki row retains the reciprocal configuration: the
remaining 4.2.9--10 contradiction is not asserted by this module.

Source: Aschbacher--Smith, 4.2.5--8, printed p.609.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
variable {G : Type*} [Group G] [Finite G]

/-- The complete ambient contrary branch on the original fixed-residual witnesses. -/
theorem reciprocal_case_of_not_unique {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ReciprocalCase L V A := by
  obtain ⟨J,H,W,hw,_⟩ := aligned_witness_of_not_unique h D hM A hAN hcomm ho hAV hnot
  refine ⟨J,H,W,hw,?_⟩
  intro hf
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hn,hcommV,hVL,⟨e,he⟩,hrest⟩
  let M := normalizer (L : Set G)
  let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let := h.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  have hne : H ≠ M := fun he => hstrict.ne (by rw [he,inf_idem])
  have hs := h.simpleQTKE.twoLocal_sqtk hM.1.1
  have hd := reciprocal_setup hH hM.1 hs hne hf
  have hB : B = L := residual_eq_of_fitting_contained L.le_normalizer le_rfl
    hH hM.1 hs hne hcover hf
  obtain ⟨hcomp,hnorm,hi⟩ := index_two_of_fitting_contained hc hn hstrict hd.1 hf
  change (B.subgroupOf H).IsCComponent at hcomp
  have hLH : L ≤ H := hB ▸ hc.component_le.trans inf_le_left
  have hVL' : V ≤ L := hB ▸ hVL
  let := D.elementary
  have hVcore : V ≤ L.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVL' D.normalizes
  have hcore : L.pCoreIn 2 ≠ ⊥ := fun he => D.ne_bot (bot_unique (he ▸ hVcore))
  have hcompL : (L.subgroupOf H).IsCComponent := hB ▸ hcomp
  have hnormL : normalizer (L.subgroupOf H : Set H) = M.subgroupOf H := hB ▸ hnorm
  exact ⟨hB,hcompL,hnormL,hi,conjugateSpan_le_intersection hLH L.le_normalizer hi,
    conjugateSpan_normalizer hH hLH hcompL hcore,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2⟩

/-- The unitary row has the full required escape on the unchanged witnesses. -/
theorem unitary_escape_case_of_not_unique {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    {s : ℕ} (hs : 2 ≤ s)
    (hu : ClassicalGroup.IsPSU ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) 3 (2 ^ s))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    EscapeCase L V A := by
  obtain ⟨J,H,W,hw,hr⟩ := reciprocal_case_of_not_unique h D hM A hAN hcomm ho hAV hnot
  refine ⟨J,H,W,hw,?_⟩
  intro hf
  obtain ⟨hB,hcomp,hnorm,hi,hrest⟩ := hr hf
  have hBH : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype ≤ H :=
    (map_subtype_le _).trans inf_le_right
  have hLH : L ≤ H := hB ▸ hBH
  let e : (L.subgroupOf H) ≃* L := subgroupOfEquivOfLe hLH
  let q : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hc := hw.2.2.2.2.2.2.1
  let : (L.subgroupOf H).Normal := normal_of_unitary_central_core_quotient hc.sqtk hcomp hs
    (hu.of_mulEquiv (centerQuotientCongr q))
  rw [normalizer_eq_top] at hnorm
  have he : (normalizer (L : Set G)).subgroupOf H = ⊤ := hnorm.symm
  rw [he,index_top] at hi
  norm_num at hi
end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape

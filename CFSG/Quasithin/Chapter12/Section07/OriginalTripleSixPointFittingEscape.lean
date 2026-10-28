module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPushingUpAt
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointTheta
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Normalizer
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ComponentEscape
public import Theory.GroupTheory.CComponent.ContainedGeneralizedFitting
public import Theory.GroupTheory.GeneralizedFitting.PreimageMovement

/-!
# The generalized Fitting preimage escapes the original triple-six point normalizer

If the preimage were contained in Mt, its two-core comparison would put
the whole two-core of the normalized Lt into O2(H). The original A5
quotient therefore promotes Lt to an ambient C-component. Its normalizer
has index at most two. In the proper case Mt has index two and is normal;
the proved identity Lt=theta(Mt) then makes Lt normal too, contradicting
the original C.2.12 normalizer identity.

No identification of blockU(Lt) with the chosen module is required.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004, C.2.13,
C.4.8(10) and the proof of 12.7.5, printed pp.148,153,840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open ChapterA.Section03.OddPrime.SourceModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual contained-preimage alternative of C.4.8 is impossible at a
proper original triple-six point centralizer. -/
theorem original_tripleSix_point_fitting_escape_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hproper : normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G) <
      centralizer ({(t : G)} : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Mt := normalizer (K : Set G) ⊓ H
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ Mt.subgroupOf H := by
  dsimp only
  intro hf
  let H := centralizer ({(t : G)} : Set G)
  let M := normalizer (K : Set G) ⊓ H
  let C := K ⊓ H
  let B := (pResidual 2 C).map C.subtype
  let A := B.subgroupOf H
  let N := M.subgroupOf H
  have h28 := original_tripleSix_pushingUp_at h structural D a t ht heven
  have hBM : B ≤ M := (map_subtype_le _).trans (inf_le_inf K.le_normalizer le_rfl)
  have hBH : B ≤ H := hBM.trans inf_le_right
  have hn : M ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hBM).mp
      (tripleSixPointResidual_component D a t ht heven).1
  have hs : conjugateSpanBy B M = B :=
    (tripleSixPointResidual_component D a t ht heven).2.2.2
  let e : A ≃* B := subgroupOfEquivOfLe hBH
  let eQ : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      (tripleSixPointResidualQuotientEquiv D a t ht heven)
  let : Group.IsPerfect B := tripleSixPointCentralizerResidual_perfect D a t ht heven
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eQ.symm
  have hAN : A ≤ N := comap_mono hBM
  have hNA : N ≤ normalizer (A : Set H) := by
    rw [← subgroupOf_normalizer_eq hBH]
    exact comap_mono hn
  have hQN : pCore 2 H ≤ N := by
    apply le_trans ?_ hf
    simpa only [QuotientGroup.ker_mk'] using
      MonoidHom.ker_le_comap (QuotientGroup.mk' (pCore 2 H)) (generalizedFitting (H ⧸ pCore 2 H))
  have hcore : A.pCoreIn 2 ≤ pCore 2 H :=
    (pCoreIn_mono_of_normalizes hAN hNA).trans
      (pCoreIn_le_of_generalizedFitting_preimage_le N hf)
  have hU : (⁅pCore 2 A, (⊤ : Subgroup A)⁆).map A.subtype ≤ pCore 2 H :=
    (map_mono (commutator_le_left _ _)).trans hcore
  have hA : A.IsCComponent :=
    isCComponent_of_contained_generalizedFitting A N hAN hNA hQN hU hf
  have hnorm : H ⊓ normalizer (B : Set G) = M := by
    have hh := h28.normalizer_span_eq
    change H ⊓ normalizer (conjugateSpanBy B M : Set G) = M at hh
    rwa [hs] at hh
  have hnormalizer : normalizer (A : Set H) = N := by
    rw [← subgroupOf_normalizer_eq hBH]
    ext x
    change (x : G) ∈ normalizer (B : Set G) ↔ (x : G) ∈ M
    exact ⟨fun hx => hnorm ▸ (show (x : G) ∈ H ⊓ normalizer (B : Set G) from ⟨x.property, hx⟩),
      fun hx => (show (x : G) ∈ H ⊓ normalizer (B : Set G) from hnorm.symm ▸ hx).2⟩
  have hsq : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_, h28.sqtk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (h28.sqtk.stronglyQuasithin p hp ho)
  have hnot : ¬ A.Normal := by
    intro hnormal
    let := hnormal
    have he : N = ⊤ := hnormalizer.symm.trans (normalizer_eq_top A)
    exact hproper.not_ge (subgroupOf_eq_top.mp he)
  have hindex : N.index = 2 := hnormalizer ▸
    (Chapter1.Section02.proposition_1_2_1_three_orbit_source hsq hA).resolve_left hnot
  let : N.Normal := normal_of_index_eq_two hindex
  have hHM : H ≤ normalizer (M : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show M ≤ H from inf_le_right)).mp inferInstance
  have htheta : (theta M).Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro f
    rw [theta, MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro _ ⟨x, hx, rfl⟩
    exact subset_closure ((f.orderOf_eq x).trans hx)
  let := htheta
  have hHB : H ≤ normalizer (B : Set G) := by
    have he : B = (theta M).map M.subtype :=
      tripleSixPointCentralizerResidual_theta h.toHypothesis1221 D a t ht heven
    rw [he]
    exact hHM.trans (normalizer_le_normalizer_characteristic_image M (theta M))
  have he : H = M := (inf_eq_left.mpr hHB).symm.trans hnorm
  exact hproper.ne he.symm

end CFSG.Quasithin.Chapter12.Section07

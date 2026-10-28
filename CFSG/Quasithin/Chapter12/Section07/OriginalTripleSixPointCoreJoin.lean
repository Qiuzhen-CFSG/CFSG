module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointComponent
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SectionCentralizer

/-!
# The original point residual retains the two-core of KT

The exact point-centralizer projection places its whole two-core in the
original component's two-core. Hence the perfect point residual's two-core
lies in Q = O2(KT). Restricting the quotient of LtQ by Q to Lt gives the
same A5 quotient. Therefore O2(LtQ) is exactly the original Q.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 12.7.4--5
and the use of 12.2.12(2), printed pp.839--840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem core_join_eq (B Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hnQ : B ≤ normalizer (Q : Set G)) (hcore : B.pCoreIn 2 ≤ Q) :
    (B ⊔ Q).pCoreIn 2 = Q := by
  let J := B ⊔ Q
  let : (Q.subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer hnQ
  let : (Q.subgroupOf J).Normal := normal_subgroupOf_sup_of_le_normalizer hnQ
  have hQB : Q.subgroupOf B = pCore 2 B := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, hQ.comap_subtype⟩
    · intro b hb
      exact hcore (mem_map_of_mem B.subtype hb)
  let e : (J ⧸ Q.subgroupOf J) ≃* (B ⧸ pCore 2 B) :=
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient B Q hnQ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hQB)
  have hzero : pCore 2 (J ⧸ Q.subgroupOf J) = ⊥ := by
    apply (map_injective (f := e.toMonoidHom) e.injective)
    rw [pCore_map_iso, Subgroup.map_bot, pCore_quotient_pCore_eq_bot]
  have hk : IsPGroup 2 (QuotientGroup.mk' (Q.subgroupOf J)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hQ.comap_subtype
  have hc := (QuotientGroup.mk' (Q.subgroupOf J)).comap_pCore_of_ker_isPGroup
    (QuotientGroup.mk'_surjective _) hk
  rw [hzero, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hc
  change (pCore 2 J).map J.subtype = Q
  rw [← hc, map_subgroupOf_eq_of_le (show Q ≤ J from le_sup_right)]

/-- The actual point-centralizer two-core lies in the original component core. -/
theorem tripleSixPointCentralizer_core_le (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    (K ⊓ centralizer ({(t : G)} : Set G)).pCoreIn 2 ≤ K.pCoreIn 2 := by
  rintro x ⟨c, hc, rfl⟩
  have hm := (tripleSixPointCentralizerProjection_ker_eq_core D a t ht heven).symm ▸ hc
  rw [tripleSixPointCentralizerProjection_ker] at hm
  exact ⟨inclusion (inf_le_left : K ⊓ centralizer ({(t : G)} : Set G) ≤ K) c, hm, rfl⟩

/-- The whole intrinsic two-core of the literal ambient Lt lies in Q=O2(KT). -/
theorem tripleSixPointResidual_core_le (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype
    Lt.pCoreIn 2 ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  have hn : C ≤ normalizer ((pResidual 2 C).map C.subtype : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  exact ((pCoreIn_mono_of_normalizes (map_subtype_le _) hn).trans
    (tripleSixPointCentralizer_core_le D a t ht heven)).trans
      (pCoreIn_mono_of_normalizes le_sup_left
        (sup_le K.le_normalizer D.sylow_normalizes_component))

/-- Joining the actual point residual with the original Q retains exactly Q
as its two-core; no point-normalizer quotient assumption is needed. -/
theorem tripleSixPointResidual_core_join (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype
    let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
    (Lt ⊔ Q).pCoreIn 2 = Q := by
  let J := K ⊔ (T : Subgroup G)
  have hn : J ≤ normalizer (J.pCoreIn 2 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  exact core_join_eq _ _ (isPGroup_pCoreIn 2 J)
    (((map_subtype_le _).trans (inf_le_left.trans le_sup_left)).trans hn)
    (tripleSixPointResidual_core_le D a t ht heven)

/-- The literal intersection of Lt and the original Q is O2(Lt). -/
theorem tripleSixPointResidual_inf_core (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype
    Lt ⊓ (K ⊔ (T : Subgroup G)).pCoreIn 2 = Lt.pCoreIn 2 := by
  apply le_antisymm
  · exact inf_pCoreIn_le_of_le 2 ((map_subtype_le _).trans (inf_le_left.trans le_sup_left))
  · exact le_inf (pCoreIn_le 2 _) (tripleSixPointResidual_core_le D a t ht heven)

/-- The entire original Q centralizes the section Lt/O2(Lt) in the literal Mt. -/
theorem tripleSixPointResidual_core_le_sectionCentralizer (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype
    (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      ChapterA.Section04.twoSectionCentralizer Lt
        (normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G)) := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let B := (pResidual 2 C).map C.subtype
  let J := K ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let H := centralizer ({(t : G)} : Set G)
  let M := normalizer (K : Set G) ⊓ H
  have hBM : B ≤ M := (map_subtype_le _).trans (inf_le_inf K.le_normalizer le_rfl)
  have hQM : Q ≤ M := le_inf
    ((pCoreIn_le 2 J).trans (sup_le K.le_normalizer D.sylow_normalizes_component))
    (D.core_centralizes.trans (centralizer_le (Set.singleton_subset_iff.mpr t.property)))
  have hnB : Q ≤ normalizer (B : Set G) := hQM.trans
    ((normal_subgroupOf_iff_le_normalizer hBM).mp
      (tripleSixPointResidual_component D a t ht heven).1)
  have hnQ : B ≤ normalizer (Q : Set G) :=
    ((map_subtype_le _).trans (inf_le_left.trans le_sup_left)).trans
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  apply (ChapterA.Section04.le_twoSectionCentralizer_iff B M Q).mpr
  refine ⟨hQM, hnB, ?_⟩
  rw [← tripleSixPointResidual_inf_core D a t ht heven]
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hnB)
    (le_normalizer_iff_commutator_le_right.mp hnQ)

end CFSG.Quasithin.Chapter12.Section07

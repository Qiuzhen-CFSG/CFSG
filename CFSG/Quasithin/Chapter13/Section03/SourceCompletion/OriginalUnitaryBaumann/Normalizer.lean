module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.Applicability
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.Source
public import Stellmacher.BaumannMap

/-!
# Normalizer control for the original unitary point radical

Uniqueness over LT controls every nontrivial subgroup normal in LT. Hence
the characteristic-normal alternative of C.1.37 controls the ambient
Baumann normalizer. In the centralizing Thompson branch B.2.10 supplies
normality directly. The latter argument applies to every overgroup of T
inside LT, and in particular to the literal original L₁T.

Source: Aschbacher--Smith 13.3.10(2), p.887, and C.1.37, p.141.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The characteristic-normal branch controls the original ambient normalizer. -/
theorem unitary_baumann_normalizer_of_characteristic
    (h : Hypothesis1331 T L) (chosen : ChosenModule T L V)
    (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (R : Subgroup G) (hRX : R ≤ L ⊔ (T : Subgroup G))
    (C : Subgroup (ChapterB.baumann R)) [C.Characteristic] (hne : C ≠ ⊥)
    (hn : L ⊔ (T : Subgroup G) ≤
      normalizer (C.map (ChapterB.baumann R).subtype : Set G)) :
    normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G) := by
  have h12 := (unitary_original_hypothesis1223 h hmax eL).toHypothesis1221
  have hCne : C.map (ChapterB.baumann R).subtype ≠ ⊥ := by
    intro hz
    exact hne ((C.map_eq_bot_iff_of_injective (ChapterB.baumann R).subtype_injective).mp hz)
  exact (normalizer_le_normalizer_characteristic_image (ChapterB.baumann R) C).trans
    (chosen.normal_subgroup_normalizer_le h12
      ((map_subtype_le _).trans (inf_le_left.trans hRX)) hCne hn)

/-- B.2.10 controls the Baumann normalizer whenever the point Thompson
subgroup centralizes the original chosen module. -/
theorem unitary_baumann_normalizer_of_thompson_centralizes
    (h : Hypothesis1331 T L) (chosen : ChosenModule T L V)
    (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
    (hPX : P ≤ L ⊔ (T : Subgroup G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (P.pCoreIn 2) ≤ centralizer (V : Set G)) :
    normalizer (ChapterB.baumann (P.pCoreIn 2) : Set G) ≤ normalizer (L : Set G) := by
  let X := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf X
  let R := (P.pCoreIn 2).subgroupOf X
  have hVX : V ≤ X := chosen.le_sylow.trans le_sup_right
  have hRX : P.pCoreIn 2 ≤ X := (map_subtype_le _).trans hPX
  let : U.Normal := normal_subgroupOf_of_le_normalizer (sup_le chosen.normalizes hTV)
  let : IsElementaryAbelian 2 V := chosen.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVX (p := 2)
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  have hQ : X.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G) :=
    (unitary_chosen_sylow_kernel chosen eL.isSimpleGroup hTV).symm
  have hQP : X.pCoreIn 2 ≤ P := hQ ▸ inf_le_left.trans hTP
  have hQR : X.pCoreIn 2 ≤ P.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X) hQP
      (hPX.trans (X.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hUR : U ≤ R := fun _ hx => hQR (chosen.le_core hx)
  have hcoreR : pCore 2 X ≤ R := fun x hx => hQR (mem_map_of_mem X.subtype hx)
  have hcore : pCore 2 X = R ⊓ centralizer (U : Set X) := by
    apply map_injective X.subtype_injective
    rw [map_inf _ _ _ X.subtype_injective,map_centralizer_subtype,
      map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hVX]
    change X.pCoreIn 2 = _
    apply le_antisymm
    · exact le_inf hQR (le_inf (map_subtype_le _) chosen.core_centralizes)
    · intro x hx
      rw [hQ]
      refine ⟨?_,hx.2.2⟩
      have hs := pCoreIn_le_sylow P (T.subtype hTP)
      have hRT : P.pCoreIn 2 ≤ (T : Subgroup G) := by
        simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP] using hs
      exact hRT hx.1
  have hJU : ChapterB.thompsonJ R 0 ≤ centralizer (U : Set X) := by
    rw [ChapterB.thompsonJ_zero]
    intro x hx y hy
    apply Subtype.ext
    have hm := mem_map_of_mem X.subtype hx
    rw [←Stellmacher.elementaryAbelianMaxJ_map_injective _ X.subtype_injective,
      map_subgroupOf_eq_of_le hRX] at hm
    exact hJ hm y hy
  have hn : (ChapterB.baumann R).Normal :=
    (ChapterB.lemma_B_2_10_centralizing U R hUR hcoreR hcore hJU).2.2.2
  have hRne : R ≠ ⊥ := by
    intro hz
    have hu : U = ⊥ := le_bot_iff.mp (hUR.trans_eq hz)
    have hu' := congrArg (map X.subtype) hu
    rw [map_subgroupOf_eq_of_le hVX,Subgroup.map_bot] at hu'
    exact chosen.ne_bot hu'
  have hBne := ChapterC.RankOne.SymmetricSix.baumann_ne_bot R
    (isPGroup_pCoreIn 2 P).comap_subtype hRne
  have hmap : (ChapterB.baumann R).map X.subtype = ChapterB.baumann (P.pCoreIn 2) := by
    have hb : (ChapterB.baumann R).map X.subtype = ChapterB.baumann (R.map X.subtype) :=
      Stellmacher.baumann_map_injective X.subtype X.subtype_injective R
    rw [hb,map_subgroupOf_eq_of_le hRX]
  rw [←hmap]
  apply chosen.normal_subgroup_normalizer_le
    (unitary_original_hypothesis1223 h hmax eL).toHypothesis1221 (map_subtype_le _) ?_ ?_
  · intro hz
    exact hBne (((ChapterB.baumann R).map_eq_bot_iff_of_injective X.subtype_injective).mp hz)
  · apply le_normalizer_iff.mpr
    rintro x hx a ⟨a,ha,rfl⟩
    exact mem_map_of_mem X.subtype (hn.conj_mem a ha ⟨x,hx⟩)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion

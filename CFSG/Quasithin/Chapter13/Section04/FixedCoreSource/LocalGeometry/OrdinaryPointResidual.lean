module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredSelection
public import Theory.GroupTheory.PResidual.IndexThreeNormalized

/-!
# The ordinary point-residual clause at the original core

The source supplement N_G(L)=LT places every two-perfect subgroup of
N_G(L) inside L: the quotient by L is a two-group. For a subgroup
normalized by the full centralizer of a Sylow-central nonfixed vector z,
the actual Sylow intersection of C_L(z) normalizes it. The ordinary
five-dimensional marking gives that Sylow subgroup index three, forcing
the subgroup to be trivial or the literal O²(C_L(z))=O^{3′}(C_L(z)).
Its intrinsic two-core quotient has order three.

This proves exactly the 13.3.9 premise used by original solvable recognition
in the ordinary row, retaining the actual N_G(L)=LT source premise. No
four-dimensional module, normality in ambient G, or selected residual is
assumed. OrdinarySource supplies the actual recognition application.
Source: Aschbacher--Smith 13.3.9 and 13.4.4(2), printed pp.887 and 897.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V Y : Subgroup G}

omit [Finite G] in
private theorem twoPerfect_le_component
    (D : ChosenModule T L V)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) : Y ≤ L := by
  let M := normalizer (L : Set G)
  let A := L.subgroupOf M
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hs : A ⊔ (T : Subgroup G).subgroupOf M = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le L.le_normalizer,
      map_subgroupOf_eq_of_le hTM,←MonoidHom.range_eq_map,range_subtype]
    exact hM.symm
  have hq : IsPGroup 2 (M ⧸ A) :=
    isPGroup_quotient_of_sup_eq_top A _ T.isPGroup'.comap_subtype hs
  have hp' : IsPPerfect 2 (Y.subgroupOf M) := hp.of_surjective
    (subgroupOfEquivOfLe hYM).symm.toMonoidHom (subgroupOfEquivOfLe hYM).symm.surjective
  have hi : Y.subgroupOf M ≤ A :=
    (le_pResidual_of_isPPerfect _ hp').trans (sInf_le ⟨inferInstance,hq⟩)
  intro y hy
  exact hi (show (⟨y,hYM hy⟩ : M) ∈ Y.subgroupOf M from hy)

/-- The literal ordinary 13.3.9 clause at either nonfixed Sylow-central weight. -/
theorem ordinary_point_residual
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hYH : Y ≤ centralizer ({z.val} : Set G))
    (hnY : centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3) := by
  have hYL := twoPerfect_le_component D hM hYM hp
  let H := centralizer ({z.val} : Set G)
  let C := L ⊓ H
  have hYC : Y ≤ C := le_inf hYL hYH
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hnC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf D.sylow_normalizes_component (hTH.trans H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let J := C ⊔ (T : Subgroup G)
  let A := C.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hnC)
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal A
  let e := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hST : ∀ s ∈ (S : Subgroup C), s.val ∈ (T : Subgroup G) := by
    rintro s ⟨a,ha,rfl⟩
    rw [hP] at ha
    exact ha
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup
  obtain ⟨eC⟩ := component_centralizer_quotient D m hcore z hzL
  have hi : (S : Subgroup C).index = 3 := SymmetricThreeTwoCore.sylow_index_three eC S
  have hp' : IsPPerfect 2 (Y.subgroupOf C) := hp.of_surjective
    (subgroupOfEquivOfLe hYC).symm.toMonoidHom (subgroupOfEquivOfLe hYC).symm.surjective
  have hn : (S : Subgroup C) ≤ normalizer (Y.subgroupOf C : Set C) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro y
    exact mem_normalizer_iff.mp (hnY (hTH (hST s hs))) y.val
  rcases eq_bot_or_residual_of_index_three (S : Subgroup C) (Y.subgroupOf C)
    S.isPGroup' hi hp' hn with hb | hr
  · left
    have hh := congrArg (map C.subtype) hb
    simpa only [map_subgroupOf_eq_of_le hYC,Subgroup.map_bot] using hh
  · have he : Y = firstCentralizerResidual L z.val := by
      have hh := congrArg (map C.subtype) hr
      rw [map_subgroupOf_eq_of_le hYC,
        twoResidual_eq_primeToResidual_three (component_centralizer_twoThree D m eL z hzL)] at hh
      exact hh.trans (firstCentralizerResidual_eq L z.val).symm
    right
    refine ⟨?_,?_⟩
    · simpa only [selectedFirstResidual,if_pos (show Nonempty ((L ⧸ pCore 2 L) ≃*
        alternatingGroup (Fin 6)) from ⟨eL⟩)] using he
    · rw [he]
      exact firstCentralizerResidual_core_quotient_card D m hcore z hzL

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry

module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.JoinCoverage
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedImages

/-!
# The original paired Baumann image

Apply the paired natural calculation to W_K inside the actual join K∨Tᵥ.
The join maps onto the full plus actor as soon as Lᵥ⁺ lies in K₋⁺. Exact
conjugation coordinates transport the module and its best offenders, while
the orbit commutator proves Thompson movement. The result identifies the
image of the original Baum(Tᵥ), without a minimal-parabolic hypothesis.

Source: Aschbacher--Smith 13.6.14 and E.2.3(2), pp.929 and216--217.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]

private theorem offender_le_of_linearEquiv {D U W : Type*} [Group D]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D U) (σ : Representation (ZMod 2) D W)
    (e : U ≃ₗ[ZMod 2] W) (he : ∀ g u, e (ρ g u) = σ g (e u)) :
    offenderSubgroup ρ ≤ offenderSubgroup σ := by
  have hw (B : Subgroup D) : weight ρ B = weight σ B := by
    have h := fixedSpace_map_equivariant ρ σ (MonoidHom.id D) e he B
    rw [Subgroup.map_id] at h
    unfold weight
    rw [←h,LinearEquiv.finrank_map_eq]
  unfold offenderSubgroup generatedBy
  refine iSup_le fun B => iSup_le fun hB => ?_
  have hb : IsBestOffender σ B := ⟨hB.1.1,fun C hC => by
    rw [←hw C,←hw B]
    exact hB.1.2 C hC⟩
  exact le_iSup_of_le B (le_iSup_of_le ⟨hb,le_top⟩ le_rfl)

theorem paired_baumann_image_source
    (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hK : K ∈ Yz L T z v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hzT : z ∈ Tv T v)
    (hLv : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (F : Type*) [Field F] [Finite F] [Algebra (ZMod 2) F]
    (e : plusImage K L T z v hL hz (Kminus K T v) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) (Gplus K L T z v hL hz) ((Fin 2 → F) × (Fin 2 → F)))
    (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : plusImage K L T z v hL hz (Kminus K T v)) (a b : Fin 2 → F),
      ρ (g : Gplus K L T z v hL hz) (a,b) = ((e g).1.val.mulVec a,(e g).2.val.mulVec b))
    (f : Additive (WK K L T z v) →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F)))
    (hf : Function.Surjective f)
    (he : ∀ g w, f (wkRepresentation K L T z v hL hz g w) = ρ g (f w))
    (hY : offenderSubgroup (wkRepresentation K L T z v hL hz) ≤
      plusImage K L T z v hL hz (Kminus K T v))
    (hexchange : ∃ t : ↥(K ⊔ Tv T v), (t : G) ∈ Tv T v ∧
      ((((⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).prod ⊥).map
        ((plusImage K L T z v hL hz (Kminus K T v)).subtype.comp e.symm.toMonoidHom)).map
          (MulAut.conj (joinPlusMap K L T z v hL hz t)).toMonoidHom =
        ((⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).prod ⊤).map
          ((plusImage K L T z v hL hz (Kminus K T v)).subtype.comp e.symm.toMonoidHom)) ∧
      ((((⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).prod ⊤).map
        ((plusImage K L T z v hL hz (Kminus K T v)).subtype.comp e.symm.toMonoidHom)).map
          (MulAut.conj (joinPlusMap K L T z v hL hz t)).toMonoidHom =
        ((⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).prod ⊥).map
          ((plusImage K L T z v hL hz (Kminus K T v)).subtype.comp e.symm.toMonoidHom))) :
    plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) =
      plusImage K L T z v hL hz (Tv T v) ⊓ plusImage K L T z v hL hz (Kminus K T v) := by
  let H := K ⊔ Tv T v
  let W := (WK K L T z v).subgroupOf H
  let C := plusImage K L T z v hL hz (Kminus K T v)
  let q := joinPlusMap K L T z v hL hz
  have hWH := WK_le_join_of_plus_placement_source K L T z v hL hz hzT hLv
  have hHG : H ≤ Gv v := sup_le hK.1.1 inf_le_right
  let : W.Normal := normal_subgroupOf_of_le_normalizer
    ((sup_le (K_le_plusActor K L T v) le_sup_right).trans
      (plusActor_normalizes_WK K L T z v hL hz))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hWH
  let := plusImage_Kminus_normal_source K L T z v hL hz hK
  have hq := joinPlusMap_surjective_of_plus_placement_source K L T z v hL hz hLv
  have hk : q.ker = centralizer (W : Set H) := by
    rw [show q.ker = (centralizer (WK K L T z v : Set G)).subgroupOf H from
      joinPlusMap_ker_source K L T z v hL hz]
    ext a
    constructor
    · intro ha w hw
      exact Subtype.ext (ha w hw)
    · intro ha w hw
      exact congrArg Subtype.val (ha ⟨w,hWH hw⟩ hw)
  let τ := NormalElementaryQuotient.representation W q hq hk
  let E : Additive W ≃ₗ[ZMod 2] Additive (WK K L T z v) :=
    { (subgroupOfEquivOfLe hWH).toAdditive with
      map_smul' := ZMod.map_smul (subgroupOfEquivOfLe hWH).toMonoidHom.toAdditive }
  have hE : ∀ g w, E (τ g w) = wkRepresentation K L T z v hL hz g (E w) := by
    intro g w
    obtain ⟨a,rfl⟩ := hq g
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (congrArg Subtype.val (NormalElementaryQuotient.representation_apply W q hq hk a w)).trans
      (wkRepresentation_apply K L T z v hL hz
        (inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) a) (E w)).symm
  obtain ⟨P,hP⟩ := hSylow.restrict (show Tv T v ≤ H from le_sup_right) hHG
  have hJ : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) := by
    intro hJ
    have hjzero : plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)) = ⊥ := by
      rw [←hP,elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      have hm : ((elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype).subgroupOf H =
          elementaryAbelianMaxJ (P : Subgroup H) := comap_map_eq_self_of_injective H.subtype_injective _
      rw [←joinPlusMap_image_source K L T z v hL hz _ (map_subtype_le _),hm]
      exact (Subgroup.map_eq_bot_iff _).mpr (hk.symm ▸ hJ)
    have hh := orbit_plus_commutator_source K L T z v hL hz hK
    rw [hjzero,commutator_bot_right] at hh
    exact plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK
      (bot_unique ((map_mono (comap_mono (le_conjugateSpanBy K (Tv T v)))).trans hh.symm.le))
  have he' : ∀ g w, (f.comp E.toLinearMap) (τ g w) = ρ g ((f.comp E.toLinearMap) w) := by
    intro g w
    exact (congrArg f (hE g w)).trans (he g (E w))
  have hx : ∃ t ∈ (P : Subgroup H),
      ((((⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).prod ⊥).map
        (C.subtype.comp e.symm.toMonoidHom)).map (MulAut.conj (q t)).toMonoidHom =
          ((⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).prod ⊤).map
            (C.subtype.comp e.symm.toMonoidHom)) ∧
      ((((⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).prod ⊤).map
        (C.subtype.comp e.symm.toMonoidHom)).map (MulAut.conj (q t)).toMonoidHom =
          ((⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).prod ⊥).map
            (C.subtype.comp e.symm.toMonoidHom)) := by
    obtain ⟨t,ht,hx⟩ := hexchange
    refine ⟨t,?_,hx⟩
    have hp : (P : Subgroup H) = (Tv T v).subgroupOf H := by
      rw [←hP]
      exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
    exact hp.symm ▸ ht
  have hB := (ChapterB.RankOneBaumann.paired_images_and_fixedSpace P W q hq hk
    ((IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal P) hJ C e ρ hfaith hnat
      (f.comp E.toLinearMap) (hf.comp E.surjective) he'
      ((offender_le_of_linearEquiv τ _ E hE).trans hY) hx).1.2
  have hm : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann (Tv T v) := by
    simpa only [ChapterB.baumann,ChapterB.thompsonAlpha,hP] using
      baumann_map_injective H.subtype H.subtype_injective (P : Subgroup H)
  have hBi : (ChapterB.baumann (Tv T v)).subgroupOf H = ChapterB.baumann (P : Subgroup H) := by
    rw [←hm]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hPi : (Tv T v).subgroupOf H = (P : Subgroup H) := by
    rw [←hP]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  rw [←joinPlusMap_image_source K L T z v hL hz (ChapterB.baumann (Tv T v)) (inf_le_left.trans le_sup_right),hBi,
    ←joinPlusMap_image_source K L T z v hL hz _ le_sup_right,hPi]
  exact hB

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection

module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentGeometry
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.ElementaryThompsonFrattini
/-!
# Characteristic control in the residual Baumann extension

Let `B = Baum(T)` and `N = O²(G) B`. The group `N` is normal and inherits
characteristic two. If no nontrivial characteristic subgroup of `B` is normal
in `G`, its characteristic normalizers lie in the unique maximal overgroup of
`T`. When `B` is a Sylow subgroup of `N`, this gives a proper control subgroup
inside `N`, without requiring `N` to be minimal parabolic.

Source: Aschbacher--Smith E.2.3(4), pp.216--217, and C.1.29, p.134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ThompsonAction.LinearBlockSource
open ChapterB ChapterC
universe u
variable {G : Type u} [Group G] [Finite G]

noncomputable abbrev residualBaumannJoin (T : Sylow 2 G) : Subgroup G := pResidual 2 G ⊔ baumann (T : Subgroup G)

instance residualBaumannJoin_normal (T : Sylow 2 G) : (residualBaumannJoin T).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←pResidual_sup_sylow_eq_top T]
  apply sup_le ((show pResidual 2 G ≤ residualBaumannJoin T from le_sup_left).trans (residualBaumannJoin T).le_normalizer)
  have hTB : (T : Subgroup G) ≤ normalizer (baumann (T : Subgroup G) : Set G) :=
    T.toSubgroup.le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hh : normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (residualBaumannJoin T : Set G) := by
    unfold residualBaumannJoin
    rw [sup_comm]
    exact normalizer_le_normalizer_sup_normal
  exact hTB.trans hh

theorem residualBaumannJoin_fitting (T : Sylow 2 G)
    (hf : generalizedFitting G = pCore 2 G) :
    generalizedFitting (residualBaumannJoin T) = pCore 2 (residualBaumannJoin T) :=
  ChapterC.RankOne.ChiProduct.SelectedRankOne.component_baumann_fitting T (pResidual 2 G)
    (inferInstance : (pResidual 2 G).Normal).isSubnormal le_normalizer_of_normal hf

omit [Finite G] in
private theorem characteristic_map_equivalence {A H : Type*} [Group A] [Group H]
    (e : A ≃* H) (C : Subgroup A) [C.Characteristic] : (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy,?_⟩
  exact e.apply_symm_apply (a (e y))

theorem residualBaumannJoin_control
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hno : ∀ C : Subgroup (baumann (T : Subgroup G)), C.Characteristic → C ≠ ⊥ →
      ¬ (C.map (baumann (T : Subgroup G)).subtype).Normal)
    (S : Sylow 2 (residualBaumannJoin T))
    (hS : (S : Subgroup (residualBaumannJoin T)).map (residualBaumannJoin T).subtype = baumann (T : Subgroup G)) :
    (S : Subgroup (residualBaumannJoin T)).characteristicNormalizerClosure ≤
      (minimalParabolicMax T hP).subgroupOf (residualBaumannJoin T) ∧
    (minimalParabolicMax T hP).subgroupOf (residualBaumannJoin T) ≠ ⊤ := by
  let N := residualBaumannJoin T
  let B := baumann (T : Subgroup G)
  let M := minimalParabolicMax T hP
  have hTM : (T : Subgroup G) ≤ M := (minimalParabolicMax_spec T hP).2
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    T.toSubgroup.le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hnorm (D : Subgroup B) [D.Characteristic] (hne : D ≠ ⊥) :
      normalizer (D.map B.subtype : Set G) ≤ M := by
    exact hP.1.le_maximal
      ⟨hTM,(minimalParabolicMax_spec T hP).1.covBy_top⟩
      (hTB.trans (normalizer_le_normalizer_characteristic_image B D))
      (lt_top_iff_ne_top.mpr (fun he => hno D inferInstance hne (normalizer_eq_top_iff.mp he)))
  constructor
  · let e : (S : Subgroup N) ≃* B :=
      ((S : Subgroup N).equivMapOfInjective N.subtype N.subtype_injective).trans (MulEquiv.subgroupCongr hS)
    apply (characteristicNormalizerClosure_le_iff _ _).mpr
    intro C hC hne
    let := hC
    let D := C.map e.toMonoidHom
    let : D.Characteristic := characteristic_map_equivalence e C
    have hD : D ≠ ⊥ := fun hz => hne ((C.map_eq_bot_iff_of_injective e.injective).mp hz)
    have hm : (C.map (S : Subgroup N).subtype).map N.subtype = D.map B.subtype := by
      rw [map_map,map_map]
      rfl
    intro x hx
    apply hnorm D hD
    rw [←hm]
    exact (C.map (S : Subgroup N).subtype).le_normalizer_map N.subtype (mem_map_of_mem N.subtype hx)
  · intro ht
    have hNM : N ≤ M := subgroupOf_eq_top.mp ht
    exact (minimalParabolicMax_spec T hP).1.ne_top
      (top_unique ((pResidual_sup_sylow_eq_top T).symm.le.trans
        (sup_le (le_sup_left.trans hNM) hTM)))
end CFSG.Quasithin.ChapterE.ThompsonAction.LinearBlockSource

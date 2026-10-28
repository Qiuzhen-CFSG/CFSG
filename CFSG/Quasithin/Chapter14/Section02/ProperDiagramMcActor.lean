module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramActor
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramMarkedKernel
public import Theory.GroupTheory.NormalSurjectiveAction
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramModelPair

/-!
# Extending the original marked action to a component overgroup

A component's characteristic marked kernel lets its conjugation action
extend to any overgroup in which that component is normal. The extension
contains the full inner automorphism group and agrees with the original
marked actor on H. A Borel-preserving inner actor fixes the selected
point-parabolic residual, giving the literal inner-preimage placement.

Source: Aschbacher--Smith 14.2.9 and 14.2.12--13, printed pp.983--984.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G D : Type*} [Group G] [Group D]

private theorem characteristic_comap_equivalence {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (N : Subgroup Y) [N.Characteristic] :
    (N.comap e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  have hh := characteristic_iff_le_comap.mp inferInstance (MulAut.congr e a) hx
  change e (a x) ∈ N
  change e (a (e.symm (e x))) ∈ N at hh
  simpa only [e.symm_apply_apply] using hh

@[expose] noncomputable def componentInOvergroupEquiv (H X : Subgroup G) (K : Subgroup H)
    (hKX : K.map H.subtype ≤ X) : K ≃* (K.map H.subtype).subgroupOf X :=
  (K.equivMapOfInjective H.subtype H.subtype_injective).trans
    (subgroupOfEquivOfLe hKX).symm

@[expose] noncomputable def markedOvergroupMap (H X : Subgroup G) (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (hKX : K.map H.subtype ≤ X) :
    (K.map H.subtype).subgroupOf X →* D :=
  (markedParabolicMap M K e).comp (componentInOvergroupEquiv H X K hKX).symm.toMonoidHom

theorem markedOvergroupMap_kernel_characteristic
    (H X : Subgroup G) (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (hKX : K.map H.subtype ≤ X)
    [ (markedParabolicMap M K e).ker.Characteristic ] :
    (markedOvergroupMap H X M K e hKX).ker.Characteristic := by
  rw [markedOvergroupMap, ← MonoidHom.comap_ker]
  exact characteristic_comap_equivalence _ _

@[expose] noncomputable def markedOvergroupActor
    (H X : Subgroup G) (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (hKX : K.map H.subtype ≤ X)
    [(K.map H.subtype).subgroupOf X |>.Normal]
    [(markedParabolicMap M K e).ker.Characteristic] : X →* MulAut D := by
  let := markedOvergroupMap_kernel_characteristic H X M K e hKX
  exact normalSurjectiveAction _ (markedOvergroupMap H X M K e hKX)
    ((markedParabolicMap_surjective M K e).comp
      (componentInOvergroupEquiv H X K hKX).symm.surjective)

 theorem markedOvergroupActor_apply
    (H X : Subgroup G) (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (hKX : K.map H.subtype ≤ X)
    [(K.map H.subtype).subgroupOf X |>.Normal]
    [(markedParabolicMap M K e).ker.Characteristic]
    (g : X) (x : K) :
    markedOvergroupActor H X M K e hKX g (markedParabolicMap M K e x) =
      markedParabolicMap M K e
        ((componentInOvergroupEquiv H X K hKX).symm
          (MulAut.conjNormal g (componentInOvergroupEquiv H X K hKX x))) := by
  let := markedOvergroupMap_kernel_characteristic H X M K e hKX
  simpa only [markedOvergroupActor, markedOvergroupMap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
    (normalSurjectiveAction_apply _ (markedOvergroupMap H X M K e hKX)
      ((markedParabolicMap_surjective M K e).comp
        (componentInOvergroupEquiv H X K hKX).symm.surjective) g
      (componentInOvergroupEquiv H X K hKX x))

 theorem markedOvergroupActor_inner_range
    (H X : Subgroup G) (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (hKX : K.map H.subtype ≤ X)
    [(K.map H.subtype).subgroupOf X |>.Normal]
    [(markedParabolicMap M K e).ker.Characteristic] :
    MulAut.innerSubgroup D ≤ (markedOvergroupActor H X M K e hKX).range := by
  let := markedOvergroupMap_kernel_characteristic H X M K e hKX
  exact inner_le_normalSurjectiveAction_range _ (markedOvergroupMap H X M K e hKX)
    ((markedParabolicMap_surjective M K e).comp
      (componentInOvergroupEquiv H X K hKX).symm.surjective)

 theorem markedOvergroupActor_restrict
    (H X : Subgroup G) (M K : Subgroup H) [K.Normal]
    (e : sourceImage M K ≃* D) (hKX : K.map H.subtype ≤ X)
    [(K.map H.subtype).subgroupOf X |>.Normal]
    [(markedParabolicMap M K e).ker.Characteristic]
    (g : H) (hg : (g : G) ∈ X) :
    markedOvergroupActor H X M K e hKX ⟨g,hg⟩ = markedParabolicActor M K e g := by
  ext d
  obtain ⟨x,rfl⟩ := markedParabolicMap_surjective M K e d
  rw [markedOvergroupActor_apply, markedParabolicActor_apply]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  let d := componentInOvergroupEquiv H X K hKX
  exact congrArg (fun z : (K.map H.subtype).subgroupOf X => (z : G))
    (d.apply_symm_apply (MulAut.conjNormal ⟨g,hg⟩ (d x)))

end CFSG.Quasithin.Chapter14.Section02

namespace CFSG.Quasithin.Chapter14.Section02
open Subgroup Theory.GroupTheory
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

 theorem markedOvergroupActor_inner_preimage_normalizes
    {F : Type*} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (H X A : Subgroup G) (M K : Subgroup H) [K.Normal]
    (e : sourceImage M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap M K).map e.toMonoidHom = Matrix.PSL3.LinearThree.borel F)
    (hF : Nat.card F = 2^f) (hf : 1 < f)
    (hKX : K.map H.subtype ≤ X)
    [(K.map H.subtype).subgroupOf X |>.Normal]
    [(markedParabolicMap M K e).ker.Characteristic]
    (hAH : A ≤ H) (hAM : A ≤ M.map H.subtype) :
    A ⊓ ((MulAut.innerSubgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)).comap
      (markedOvergroupActor H X M K e hKX)).map X.subtype ≤
    A ⊓ normalizer ((markedParabolicResidual M K e
      (Matrix.PSL3.LinearThree.pointParabolic F)).map H.subtype : Set G) := by
  rintro g ⟨hgA,⟨x,hx,hxg⟩⟩
  refine ⟨hgA,?_⟩
  subst g
  let g : H := ⟨x,hAH hgA⟩
  have hgM : g ∈ M := by
    obtain ⟨y,hy,hyg⟩ := hAM hgA
    exact (show y = g from Subtype.ext hyg) ▸ hy
  have hres := markedOvergroupActor_restrict H X M K e hKX g x.property
  obtain ⟨u,hu⟩ := hx
  have hin : markedParabolicActor M K e g = MulAut.conj u := hres.symm.trans hu.symm
  have hB := markedParabolicActor_borel M K e he g hgM
  have hp : (Matrix.PSL3.LinearThree.pointParabolic F).map
      (markedParabolicActor M K e g).toMonoidHom = Matrix.PSL3.LinearThree.pointParabolic F := by
    rcases Matrix.PSL3.LinearThree.point_parabolic_map_pair_of_borel F _ hB with hp | hp
    · exact hp
    · rw [hin] at hp
      exact (Matrix.PSL3.LinearThree.OuterExtensions.pointParabolic_not_conjugate_line
        F (by omega) hF u hp).elim
  have hn : g ∈ normalizer (markedParabolicResidual M K e
      (Matrix.PSL3.LinearThree.pointParabolic F) : Set H) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact markedParabolicResidual_conj M K e _ _ g hp
  exact (markedParabolicResidual M K e _).le_normalizer_map H.subtype
    (mem_map_of_mem H.subtype hn)
end CFSG.Quasithin.Chapter14.Section02

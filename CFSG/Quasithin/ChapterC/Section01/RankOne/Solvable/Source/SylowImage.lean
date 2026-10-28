module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.AmbientExtension
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Marking

public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Local block extension through an injective Sylow marking

An injective map carrying the prescribed local Sylow subgroup onto an
ambient Sylow subgroup carries the local omega normal closure onto the
corresponding closure in its image. The original Thompson commutator and
block support consequently satisfy the solvable ambient-extension theorem
on that image. This places the same block subnormally in the ambient group.

Source: Aschbacher--Smith C.1.27, printed p.133.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC
namespace GlaubermanNiles
variable {B H : Type*} [Group B] [Group H] [Finite H] {e : B →* H}
omit [Finite H] in
/-- The original marked normal closure is the native Sylow omega module. -/
theorem localV_eq_vSubgroup (he : Function.Injective e) (P : Sylow 2 H)
    (hP : e.range = (P : Subgroup H)) : localV e = SectionTwo.vSubgroup P := by
  have hω : omegaCenter B = omegaOneCenterAmbient (⊤ : Subgroup B) := by
    ext b
    simp only [mem_omegaCenter_iff,mem_omegaOneCenterAmbient_iff,mem_top,true_and]
    simp
  change normalClosure ((omegaCenter B).map e : Set H) = normalClosure (omegaOneCenterAmbient (P : Subgroup H) : Set H)
  rw [←hP,MonoidHom.range_eq_map,omegaOneCenterAmbient_map_injective e he,←hω]
end GlaubermanNiles
namespace RankOne.Solvable
universe u v
variable {A : Type u} {G : Type v} [Group A] [Group G] [Finite A] [Finite G]
/-- Literal Sylow and module transport supplies the ambient-extension application. -/
theorem subnormal_map_of_sylow_image (h : SectionTwo.Hypotheses G)
    (f : A →* G) (hf : Function.Injective f) (P : Sylow 2 A) (T : Sylow 2 G)
    (hPT : (P : Subgroup A).map f = (T : Subgroup G)) (R : Subgroup A)
    (hR : R.IsSubnormal) (ha : IsAlternatingBlock R 3)
    (hJ : R = ⁅R,elementaryAbelianMaxJ (P : Subgroup A)⁆)
    (hU : (blockU R).map R.subtype ≤ SectionTwo.vSubgroup P) :
    (R.map f).IsSubnormal := by
  let H := f.range
  let q : A →* H := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hqi : Function.Injective q := fun _ _ he => hf (congrArg Subtype.val he)
  have hTH : (T : Subgroup G) ≤ H := hPT ▸ map_le_range f P
  have hPq : (P : Subgroup A).map q = (T.subtype hTH : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [map_map,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
    exact hPT
  have hv : (SectionTwo.vSubgroup P).map q = SectionTwo.vSubgroup (T.subtype hTH) := by
    change (normalClosure (omegaOneCenterAmbient (P : Subgroup A) : Set A)).map q =
      normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H)
    rw [map_normalClosure _ q hq]
    congr 1
    rw [←Subgroup.coe_map,←omegaOneCenterAmbient_map_injective q hqi,hPq]
  have hm : (R.map f).subgroupOf H = R.map q := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (map_le_range f R),map_map]
    rfl
  let a : R ≃* R.map f := R.equivMapOfInjective f hf
  have ha' := isAlternatingBlock_of_equiv a ha
  apply isSubnormal_of_local_alternatingThree h T hTH (map_le_range f R)
  · rw [hm]
    exact hR.map hq
  · exact ha'
  · have hh := congrArg (map f) hJ
    rwa [map_commutator,←elementaryAbelianMaxJ_map_injective f hf,hPT] at hh
  · rw [←blockU_map_equiv a,map_map]
    have hh := map_mono (f := f) hU
    rw [map_map] at hh
    have hv' : (SectionTwo.vSubgroup P).map f =
        (SectionTwo.vSubgroup (T.subtype hTH)).map H.subtype := by
      rw [←hv,map_map]
      rfl
    exact hh.trans_eq hv'
end RankOne.Solvable
end CFSG.Quasithin.ChapterC

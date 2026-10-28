module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionSylowModel
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionPlaneClasses
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.InvolutionFusion
/-!
# The ordinary Sylow subgroup in the doubled source completion

The literal ordinary upper subgroup embeds in the extended overlap. Its
source image has order 64 and index two in the marked extended Sylow of
order 128. The existing point-parabolic involution-placement theorem moves
each of its involutions into the plane radical through the actual endpoint
maps. The plane class calculation then gives root-or-short fusion in the
ambient completion, without any exceptional-case assumption.

This supplies the index-two subgroup and ordinary involution coverage used
by the Thompson-transfer argument in Aschbacher--Smith F.4.38, printed p.294.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
local notation "U" => upperProjective 1 hn
local notation "B" => Extension.overlap 1 hn
local notation "P" => pointParabolic 1 hn
local notation "R" => planeParabolic 1 hn

def ordinaryUpperInclusion : U →* B :=
  ((SemidirectProduct.inl : ProjectiveGroup 1 hn →* Extension.ProjectiveExtension 1 hn).comp
    (U).subtype).codRestrict _ (fun a => (Extension.binary_mem_overlap _).mpr
      (upperProjective_le_overlap 1 hn a.property))

theorem ordinaryUpperInclusion_injective : Function.Injective ordinaryUpperInclusion := by
  intro a b h
  exact Subtype.ext (SemidirectProduct.inl_injective (congrArg Subtype.val h))

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

def sourceOrdinaryUpperMap : U →* G := (i.comp c.middle).comp ordinaryUpperInclusion
def sourceOrdinaryUpper : Subgroup G := (sourceOrdinaryUpperMap c i).range

theorem sourceOrdinaryUpperMap_injective (hi : Function.Injective i) :
    Function.Injective (sourceOrdinaryUpperMap c i) :=
  (hi.comp c.middle_injective).comp ordinaryUpperInclusion_injective

theorem sourceOrdinaryUpper_le_sylowImage : sourceOrdinaryUpper c i ≤ Source.sylowImage c i := by
  rintro _ ⟨a,rfl⟩
  refine ⟨ordinaryUpperInclusion a,?_,rfl⟩
  exact (extendedUpper_mem _).mpr a.property

theorem sourceOrdinaryUpper_card (hi : Function.Injective i) : Nat.card (sourceOrdinaryUpper c i)=64 := by
  rw [sourceOrdinaryUpper,←Nat.card_congr (MonoidHom.ofInjective
    (sourceOrdinaryUpperMap_injective c i hi)).toEquiv,upperProjective_card]
  rfl

theorem sourceOrdinaryUpper_relIndex (hi : Function.Injective i) :
    (sourceOrdinaryUpper c i).relIndex (Source.sylowImage c i)=2 := by
  have hc : Nat.card ((sourceOrdinaryUpper c i).subgroupOf (Source.sylowImage c i))=64 :=
    (Nat.card_congr (subgroupOfEquivOfLe (sourceOrdinaryUpper_le_sylowImage c i)).toEquiv).trans
      (sourceOrdinaryUpper_card c i hi)
  have hh := ((sourceOrdinaryUpper c i).subgroupOf (Source.sylowImage c i)).card_mul_index
  rw [hc,source_sylowImage_card c i hi] at hh
  change ((sourceOrdinaryUpper c i).subgroupOf (Source.sylowImage c i)).index=2
  omega

theorem sourceOrdinaryUpper_involution_to_plane_in_completion (hi : Function.Injective i)
    (x : G) (hx : x∈sourceOrdinaryUpper c i) (hx2 : x^2=1) :
    ∃ y ∈ Q c i true, ∃ g ∈ i.range, g*x*g⁻¹=y := by
  obtain ⟨a,rfl⟩ := hx
  have ha2 : a^2=1 := (sourceOrdinaryUpperMap_injective c i hi) (by
    simpa only [map_pow,map_one] using hx2)
  obtain ⟨g,q,hq,he⟩ := UnitaryTwo.InvolutionPlacement.projective_sylow_involution_placement
    a.val a.property (congrArg Subtype.val ha2)
  change q.val=g.val*a.val*g.val⁻¹ at he
  have haP : a.val ∈ P := (projectiveSylow_le_parabolics 1 hn).1 a.property
  have hqP : q.val ∈ P := by
    rw [he]
    exact (P).mul_mem ((P).mul_mem g.property haP) ((P).inv_mem g.property)
  have hqR : q.val ∈ R := L2_le_planeParabolic 1 hn q.property
  have hqB : q.val ∈ overlap 1 hn := by
    rw [←exact_overlap]
    exact ⟨hqP,hqR⟩
  let b : B := ⟨SemidirectProduct.inl q.val,(Extension.binary_mem_overlap _).mpr hqB⟩
  have hleft : Source.pointInclusion g * (Extension.amalgam 1 hn).left (ordinaryUpperInclusion a) *
      (Source.pointInclusion g)⁻¹=(Extension.amalgam 1 hn).left b := by
    apply Subtype.ext
    change SemidirectProduct.inl g.val * SemidirectProduct.inl a.val * (SemidirectProduct.inl g.val)⁻¹ = SemidirectProduct.inl q.val
    rw [←map_inv,←map_mul,←map_mul]
    exact congrArg SemidirectProduct.inl he.symm
  refine ⟨i (c.middle b),?_,?_⟩
  · rw [Q_eq_map_pCore]
    let qR : R := ⟨q.val,hqR⟩
    refine ⟨qR,?_,?_⟩
    · let e : L2 1 hn ≃* R := MulEquiv.subgroupCongr BinaryCompletion.plane_eq_local.symm
      change e q ∈ pCore 2 R
      rw [←pCore_map_iso 2 e]
      exact mem_map_of_mem e.toMonoidHom hq
    · change i (c.right (Source.planeInclusion qR))=i (c.middle b)
      rw [DFunLike.congr_fun c.compatible b]
      rfl
  · refine ⟨i (c.left (Source.pointInclusion g)),⟨c.left (Source.pointInclusion g),rfl⟩,?_⟩
    change i (c.left (Source.pointInclusion g)) * i (c.middle (ordinaryUpperInclusion a)) *
      (i (c.left (Source.pointInclusion g)))⁻¹=i (c.middle b)
    calc
      _ = i (c.left (Source.pointInclusion g * (Extension.amalgam 1 hn).left (ordinaryUpperInclusion a) *
          (Source.pointInclusion g)⁻¹)) := by
        simp only [map_mul,map_inv]
        rfl
      _ = _ := by rw [hleft]; rfl

theorem sourceOrdinaryUpper_involution_to_plane (hi : Function.Injective i)
    (x : G) (hx : x∈sourceOrdinaryUpper c i) (hx2 : x^2=1) :
    ∃ y ∈ Q c i true, IsConj x y := by
  obtain ⟨y,hy,g,_,hg⟩ := sourceOrdinaryUpper_involution_to_plane_in_completion c i hi x hx hx2
  exact ⟨y,hy,isConj_iff.mpr ⟨g,hg⟩⟩

theorem sourceOrdinaryUpper_involution_classes (z : P) (h : Source.Hypotheses c i z)
    (x : G) (hx : x∈sourceOrdinaryUpper c i) (hx2 : orderOf x=2) :
    IsConj (rootElement c i z) x ∨ IsConj (sourceMarkedShort c i) x := by
  obtain ⟨y,hy,hxy⟩ := sourceOrdinaryUpper_involution_to_plane c i h.embedding_injective x hx
    (by rw [←hx2]; exact pow_orderOf_eq_one x)
  rcases source_Q_plane_classes c i z h y hy with rfl | hr | ht
  · have hx1 := isConj_one_right.mp hxy.symm
    rw [hx1,orderOf_one] at hx2
    omega
  · exact Or.inl (hr.trans hxy.symm)
  · exact Or.inr (ht.trans hxy.symm)
/-- Plane-radical fusion is realized inside the original completion image. -/
theorem source_Q_plane_classes_in_completion (z : P) (h : Source.Hypotheses c i z)
    (x : G) (hx : x∈Q c i true) :
    x=1 ∨ ∃ g∈i.range, g*rootElement c i z*g⁻¹=x ∨ g*sourceMarkedShort c i*g⁻¹=x := by
  rw [←sourceModelPlaneMap_radical c i] at hx
  obtain ⟨a,ha,rfl⟩ := hx
  have hrange (g : L2Matrix 1 hn) : sourceModelPlaneMap c i g∈i.range :=
    ⟨c.right (Source.planeInclusion (UnitaryTwo.ShortRootFusion.matrixPlaneEquiv g)),rfl⟩
  rcases UnitaryTwo.ModelClasses.local_radical_classes a ha with he | hr | ht
  · exact Or.inl (by rw [he,map_one])
  · obtain ⟨g,hg⟩ := isConj_iff.mp hr
    refine Or.inr ⟨sourceModelPlaneMap c i g,hrange g,Or.inl ?_⟩
    rw [←sourceModelPlaneMap_long c i z h,←map_inv,←map_mul,←map_mul]
    exact congrArg (sourceModelPlaneMap c i) hg
  · obtain ⟨g,hg⟩ := isConj_iff.mp ht
    refine Or.inr ⟨sourceModelPlaneMap c i g,hrange g,Or.inr ?_⟩
    rw [←sourceModelPlaneMap_short c i,←map_inv,←map_mul,←map_mul]
    exact congrArg (sourceModelPlaneMap c i) hg

/-- Every ordinary-upper involution is conjugate to a marked root or short
involution by an element of the original completion image. -/
theorem sourceOrdinaryUpper_involution_classes_in_completion (z : P) (h : Source.Hypotheses c i z)
    (x : G) (hx : x∈sourceOrdinaryUpper c i) (hx2 : orderOf x=2) :
    ∃ g∈i.range, g*rootElement c i z*g⁻¹=x ∨ g*sourceMarkedShort c i*g⁻¹=x := by
  obtain ⟨y,hy,g,hg,hxy⟩ := sourceOrdinaryUpper_involution_to_plane_in_completion c i
    h.embedding_injective x hx (by rw [←hx2]; exact pow_orderOf_eq_one x)
  rcases source_Q_plane_classes_in_completion c i z h y hy with hy1 | ⟨k,hk,hy⟩
  · have hx1 : x=1 := by
      have hh : IsConj x 1 := isConj_iff.mpr ⟨g,hxy.trans hy1⟩
      exact isConj_one_right.mp hh.symm
    rw [hx1,orderOf_one] at hx2
    omega
  · refine ⟨g⁻¹*k,i.range.mul_mem (i.range.inv_mem hg) hk,?_⟩
    have hcomp (r : G) (hr : k*r*k⁻¹=y) : (g⁻¹*k)*r*(g⁻¹*k)⁻¹=x := by
      calc
        _ = g⁻¹*(k*r*k⁻¹)*g := by group
        _ = g⁻¹*y*g := by rw [hr]
        _ = x := by rw [←hxy]; group
    exact hy.elim (fun hr => Or.inl (hcomp _ hr)) (fun ht => Or.inr (hcomp _ ht))
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal

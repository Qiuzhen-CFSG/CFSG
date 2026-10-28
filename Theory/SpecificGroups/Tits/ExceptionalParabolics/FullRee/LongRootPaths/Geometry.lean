module

public import Theory.GroupTheory.Amalgam.RankTwoCompletion
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.LongCentralizer
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.WeylVerification
public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingPaths
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.SecondEmbedding
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.First

/-!
# The literal four-point long-root path in every faithful completion

The alternating Weyl word carries root 9 through roots 8 and 5 to the square
of root one. Each of the three conjugations lies entirely in one endpoint,
so the same identity holds in every faithful completion of the marked full
binary Ree amalgam. The two reflection escape facts construct the literal
nonbacktracking four-edge walk. Its final central involution is the original
root-one square; no global completion equivalence or smallness is used.

Source: the paragraph following J.4.7, printed p.442, using F.4.6 and the
marked long-root identities of F.4.27(4). Root conventions are those of
Shinoda (1975), pp.81–83 and Parrott (1972), p.683.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Theory.GroupTheory ReeTwo ParabolicMarkedComparison
open Tits.AmalgamRigidity.FullRee
open Subgroup
noncomputable section

def leftReflection : first := Verified.firstEquiv Centralizer.weyl
def rightReflection : second := SecondExtension.reflection
def middleRoot (i : CoreRoot) : B := borelEquiv (SylowModel.root i)
def middleRootOne : B := borelEquiv SylowModel.rootOne

theorem leftReflection_coe : (leftReflection : ReeF4.Model 0) =
    atlasEmbedding (Atlas.a .r1) := by
  rw [Atlas.a,Ambient.atlas_generator]
  exact Verified.localMap_weyl

theorem rightReflection_coe : (rightReflection : ReeF4.Model 0) =
    atlasEmbedding (Atlas.a .r8) := by
  rw [Atlas.a,Ambient.atlas_generator]
  rfl

theorem fourthWord_model :
    (rightReflection : ReeF4.Model 0) * leftReflection * rightReflection = fourthWord := by
  rw [rightReflection_coe,leftReflection_coe]
  rw [← map_mul,← map_mul]
  rfl

theorem left_root (i : CoreRoot) : amalgam.left (middleRoot i) =
    Verified.firstEquiv (Centralizer.root i) := rfl

theorem right_root (i : CoreRoot) : amalgam.right (middleRoot i) =
    SecondExtension.inclusion (SylowModel.root i) := rfl

theorem leftReflection_conjugates (i : CoreRoot) :
    leftReflection * amalgam.left (middleRoot i) * leftReflection⁻¹ =
      amalgam.left (middleRoot (weylRoot i)) := by
  rw [left_root,left_root]
  change Verified.firstEquiv Centralizer.weyl * _ * (Verified.firstEquiv Centralizer.weyl)⁻¹ = _
  rw [← map_inv,← map_mul,← map_mul,Centralizer.weyl_root]

theorem rightReflection_nine :
    rightReflection * amalgam.right (middleRoot 9) * rightReflection⁻¹ =
      amalgam.right (middleRoot 8) := SecondExtension.weyl_relations.conjugate 9

theorem rightReflection_five :
    rightReflection * amalgam.right (middleRoot 5) * rightReflection⁻¹ =
      amalgam.right (middleRootOne^2) := by
  rw [map_pow]
  exact (SecondExtension.weyl_relations.conjugate 5).trans (map_pow _ _ _)

theorem middleRoot_nine_coe : (middleRoot 9 : ReeF4.Model 0) = z :=
  (SecondExtension.inclusion_root 9).trans Verified.atlas_last_root.symm

theorem middleRootOne_square_coe : (middleRootOne^2 : B).val = u := by
  rw [u,Atlas.a,Ambient.atlas_generator]
  change (middleRootOne : ReeF4.Model 0)^2 = Ambient.rootOne * Ambient.rootOne
  rw [show (middleRootOne : ReeF4.Model 0)=Ambient.rootOne from SecondExtension.inclusion_rootOne,pow_two]

theorem leftReflection_not_middle : leftReflection ∉ amalgam.left.range := by
  rintro ⟨t,ht⟩
  obtain ⟨k,rfl⟩ := borelEquiv.surjective t
  have he : SylowModel.embedding k = Centralizer.weyl := Verified.firstEquiv.injective ht
  have hne : (SemidirectProduct.inr FiveFour.r : FirstRestrictions.E) ∉ FirstRestrictions.fromS.range := by
    rw [PointedPairs.mem_firstB_iff]
    decide +kernel
  apply hne
  refine ⟨k,?_⟩
  apply FirstRestrictions.equiv.injective
  rw [FirstRestrictions.equiv_fromS,he]
  change Centralizer.weyl = SemidirectProduct.inr (Core.complementEquiv FiveFour.r)
  rw [Core.complementEquiv_r]
  rfl

theorem rightReflection_not_middle : rightReflection ∉ amalgam.right.range := by
  rintro ⟨t,ht⟩
  obtain ⟨k,rfl⟩ := borelEquiv.surjective t
  have he : PointedPairs.secondSylow k = SemidirectProduct.inr (DihedralGroup.sr 0) := by
    apply PointedPairs.secondMap_bijective.1
    rw [PointedPairs.secondMap_secondSylow,PointedPairs.secondMap_reflection]
    exact ht
  have hn : (SemidirectProduct.inr (DihedralGroup.sr 0) : PointedPairs.SecondModel) ∉ PointedPairs.secondSylow.range := by
    rw [PointedPairs.mem_secondB_iff]
    decide +kernel
  exact hn ⟨k,he⟩

variable {G : Type*} [Group G] (c : RankTwoAmalgam.FaithfulCompletion amalgam (G:=G))

def completionFamily : Bool → Subgroup G := fun i => bif i then c.right.range else c.left.range

theorem completion_overlap : c.left.range ⊓ c.right.range = c.middle.range := by
  apply c.overlap_eq_of_gcd
  rw [first_card,second_card,borel_card]
  norm_num

theorem completion_left_not_right : c.left leftReflection ∉ c.right.range := by
  intro h
  have hm : c.left leftReflection ∈ c.middle.range :=
    completion_overlap c ▸ (show c.left leftReflection ∈ c.left.range ⊓ c.right.range from ⟨⟨leftReflection,rfl⟩,h⟩)
  obtain ⟨t,ht⟩ := hm
  exact leftReflection_not_middle ⟨t,c.left_injective ht⟩

theorem completion_right_not_left : c.right rightReflection ∉ c.left.range := by
  intro h
  have hm : c.right rightReflection ∈ c.middle.range :=
    completion_overlap c ▸ (show c.right rightReflection ∈ c.left.range ⊓ c.right.range from ⟨h,⟨rightReflection,rfl⟩⟩)
  obtain ⟨t,ht⟩ := hm
  have he : c.right (amalgam.right t) = c.right rightReflection :=
    (DFunLike.congr_fun c.compatible t).symm.trans ht
  exact rightReflection_not_middle ⟨t,c.right_injective he⟩

def completionLeftWord : G := c.left leftReflection * c.right rightReflection

theorem completion_leftSix_conjugates :
    completionLeftWord c * c.middle (middleRoot 9) * (completionLeftWord c)⁻¹ =
      c.middle (middleRoot 5) := by
  have hr (i : CoreRoot) : c.middle (middleRoot i) = c.right (amalgam.right (middleRoot i)) :=
    DFunLike.congr_fun c.compatible _
  have h9 : c.right rightReflection * c.middle (middleRoot 9) * (c.right rightReflection)⁻¹ =
      c.middle (middleRoot 8) := by
    rw [hr,hr,← map_inv,← map_mul,← map_mul,rightReflection_nine]
  have h8 : c.left leftReflection * c.middle (middleRoot 8) * (c.left leftReflection)⁻¹ =
      c.middle (middleRoot 5) := by
    change c.left leftReflection * c.left (amalgam.left (middleRoot 8)) * (c.left leftReflection)⁻¹ = _
    rw [← map_inv,← map_mul,← map_mul,leftReflection_conjugates]
    rfl
  calc
    _ = c.left leftReflection * (c.right rightReflection * c.middle (middleRoot 9) *
      (c.right rightReflection)⁻¹) * (c.left leftReflection)⁻¹ := by
        unfold completionLeftWord
        group
    _ = _ := by rw [h9,h8]


def completionFourthWord : G := c.right rightReflection * c.left leftReflection * c.right rightReflection

theorem completion_conjugates :
    completionFourthWord c * c.middle (middleRoot 9) * (completionFourthWord c)⁻¹ =
      c.middle (middleRootOne^2) := by
  have hr (i : CoreRoot) : c.middle (middleRoot i) = c.right (amalgam.right (middleRoot i)) :=
    DFunLike.congr_fun c.compatible _
  have h9 : c.right rightReflection * c.middle (middleRoot 9) * (c.right rightReflection)⁻¹ =
      c.middle (middleRoot 8) := by
    rw [hr,hr,← map_inv,← map_mul,← map_mul,rightReflection_nine]
  have h8 : c.left leftReflection * c.middle (middleRoot 8) * (c.left leftReflection)⁻¹ =
      c.middle (middleRoot 5) := by
    change c.left leftReflection * c.left (amalgam.left (middleRoot 8)) * (c.left leftReflection)⁻¹ = _
    rw [← map_inv,← map_mul,← map_mul,leftReflection_conjugates]
    rfl
  have h5 : c.right rightReflection * c.middle (middleRoot 5) * (c.right rightReflection)⁻¹ =
      c.middle (middleRootOne^2) := by
    rw [hr,show c.middle (middleRootOne^2)=c.right (amalgam.right (middleRootOne^2)) from
      DFunLike.congr_fun c.compatible _,← map_inv,← map_mul,← map_mul,rightReflection_five]
  calc
    _ = c.right rightReflection * (c.left leftReflection *
      (c.right rightReflection * c.middle (middleRoot 9) * (c.right rightReflection)⁻¹) *
        (c.left leftReflection)⁻¹) * (c.right rightReflection)⁻¹ := by
      unfold completionFourthWord
      group
    _ = _ := by rw [h9,h8,h5]

open Subgroup.CosetGeometry.RankTwo SimpleGraph.BasedWalk

def completionFourPath : SimpleGraph.BasedWalk (graph (completionFamily c)) 4
    (base (completionFamily c) false) :=
  alternatingFour (completionFamily c) (c.left leftReflection) (c.right rightReflection)
    ⟨leftReflection,rfl⟩ ⟨rightReflection,rfl⟩

theorem completionFourPath_endpoint : (completionFourPath c).endpoint =
    completionFourthWord c • base (completionFamily c) false := rfl

theorem completionFourPath_nonbacktracking : (completionFourPath c).Nonbacktracking :=
  alternatingFour_nonbacktracking (completionFamily c) _ _ _ _
    (completion_left_not_right c) (completion_right_not_left c)

theorem completion_fusion : IsConj (c.middle (middleRootOne^2)) (c.middle (middleRoot 9)) :=
  (isConj_iff.mpr ⟨completionFourthWord c,completion_conjugates c⟩).symm

theorem completion_root_order : orderOf (c.middle (middleRoot 9)) = 2 := by
  change orderOf (c.left (amalgam.left (middleRoot 9))) = 2
  rw [left_root]
  exact (orderOf_injective c.left c.left_injective _).trans
    ((Verified.firstEquiv.orderOf_eq (Centralizer.root 9)).trans
      Centralizer.root_twelve_order)

theorem completion_root_centralizes : c.left.range ≤ centralizer {c.middle (middleRoot 9)} := by
  rintro _ ⟨a,rfl⟩
  rw [mem_centralizer_singleton_iff]
  change c.left a * c.left (amalgam.left (middleRoot 9)) = c.left (amalgam.left (middleRoot 9)) * c.left a
  rw [left_root,← map_mul,← map_mul]
  apply congrArg c.left
  obtain ⟨a,rfl⟩ := Verified.firstEquiv.surjective a
  rw [← map_mul,← map_mul]
  exact congrArg Verified.firstEquiv (mem_center_iff.mp Centralizer.root_twelve_central a)

theorem completion_fourth_centralizes :
    stabilizer (completionFamily c) (completionFourPath c).endpoint ≤
      centralizer {c.middle (middleRootOne^2)} := by
  rw [completionFourPath_endpoint,stabilizer_translate]
  simp only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base]
  rintro _ ⟨a,ha,rfl⟩
  rw [mem_centralizer_singleton_iff,← completion_conjugates c]
  have hh := mem_centralizer_singleton_iff.mp (completion_root_centralizes c ha)
  change (completionFourthWord c*a*(completionFourthWord c)⁻¹) * _ = _
  simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_assoc,inv_mul_cancel_left] using
    congrArg (fun x => completionFourthWord c*x*(completionFourthWord c)⁻¹) hh

theorem leftSix_eq_rootfive : leftSix = (middleRoot 5 : ReeF4.Model 0) := by
  let q : RankTwoAmalgam.FaithfulCompletion amalgam (G:=ReeF4.Model 0) :=
    RankTwoAmalgam.FaithfulCompletion.ofSubgroups first B second borel_le_first borel_le_second generate
  have h := completion_leftSix_conjugates q
  change ((leftReflection : ReeF4.Model 0)*rightReflection) * (middleRoot 9 : ReeF4.Model 0) *
    ((leftReflection : ReeF4.Model 0)*rightReflection)⁻¹ = (middleRoot 5 : ReeF4.Model 0) at h
  rw [leftReflection_coe,rightReflection_coe,middleRoot_nine_coe] at h
  simpa only [leftSix,Atlas.leftWord,z,map_mul,map_inv] using h

theorem completion_endpoints_product_order :
    orderOf (c.middle (middleRoot 5) * c.middle (middleRootOne^2)) = 4 := by
  rw [← map_mul,orderOf_injective c.middle c.middle_injective]
  have h := leftSix_mul_u_order
  rw [leftSix_eq_rootfive,← middleRootOne_square_coe] at h
  have he := orderOf_injective B.subtype B.subtype_injective (middleRoot 5*middleRootOne^2)
  exact he.symm.trans h


end
end Tits.ExceptionalParabolics.FullRee.LongRootPaths

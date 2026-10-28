module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity.SourceGeometry
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity.SourceCore
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity.IndependentCubic
public import Theory.GroupTheory.QuaternionSwapModel.DiagonalMovement

/-!
# Original-source Aut(M₁₂) rigidity

The source pair transports the actual nonsplit first core and the separate split
movement subgroup. The corrected square-functional argument handles the third
invariant-core case. In the other cases a proper characteristic-two overgroup
contains an independent cubic on one quaternion factor. Combining it with its
factor-swap conjugate gives an element normalizing the original Thompson sixteen
and moving the original local plane. Source uniqueness forces that normalizer
to preserve the plane, so the containing centralizer equals the first parabolic.

Every marking and normalizer statement refers to the original source subgroups;
no additional residual or automorphism identification is assumed.
Source: Aschbacher–Smith 14.2.21, printed pp.988–989, with the nonsplit-core
correction described in `docs/quasithin-proof-basis.md`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
open SourcePreliminaries Chapter15.Section03 SourceModel.Transport
open QuaternionSwapModel.MarkedCubic
variable {G : Type*} [Group G] [Finite G]

/-- The original Aut(M₁₂) source row, using the nonsplit first core and the
actual marked Thompson-normalizer movement. -/
theorem source_rigidity (T : Sylow 2 G) (M Mc H : Subgroup G)
    (c : CubicSourceContext T M Mc H)
    (hmodel : ChapterF.GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
        (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right)) : H = Mc := by
  obtain ⟨r⟩ := hmodel
  by_contra hproper
  let f : QuaternionSwapModel.QH →* Mc := (movement r).codRestrict Mc
    (fun q => c.H_le_Mc (movement_mem r q).1)
  have hf : Function.Injective f := fun x y h =>
    movement_injective r (congrArg Mc.subtype h)
  have hmap (W : Subgroup QuaternionSwapModel.QH) :
      W.map f = (W.map (movement r)).subgroupOf Mc := by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨q,hq,rfl⟩
    · rintro ⟨q,hq,he⟩
      exact ⟨q,hq,Subtype.ext he⟩
  have hbase : QuaternionSwapModel.QK.map f =
      (FourWreathTwo.base.comap (wreathMap (insideRecognition c r))).map
        ((H.subgroupOf Mc).subtype.comp (pCore 2 (H.subgroupOf Mc)).subtype) := by
    rw [hmap,movement_core,wreath_preimage_inside]
  have hZ : QuaternionSwapModel.Z.map f ≤ center Mc := by
    rw [hmap,source_movement_mark c r]
    intro z hz
    apply mem_center_iff.mpr
    intro m
    apply Subtype.ext
    have hm : (m : G) ∈ centralizer (centralInvolutions T : Set G) := by
      rw [← c.Mc_centralizer]
      exact m.property
    exact (hm z hz).symm
  let S := T.subtype (c.sylow_le_H.trans c.H_le_Mc)
  have hSH : (S : Subgroup Mc) ≤ H.subgroupOf Mc := fun _ hx => c.sylow_le_H hx
  have hp : H.subgroupOf Mc ≠ ⊤ := by
    intro he
    apply hproper
    apply le_antisymm c.H_le_Mc
    intro x hx
    exact show (⟨x,hx⟩ : Mc) ∈ H.subgroupOf Mc from he.ge (mem_top _)
  obtain ⟨_,hc,u,hu,huB,huC,hune⟩ := independent_cubic_of_proper_overgroup
    (H.subgroupOf Mc) (insideRecognition c r) f hf hbase S hSH
    (marked_center_inside c r) c.Mc_characteristic_two hp
  obtain ⟨g,_,hg,hmove⟩ := QuaternionSwapModel.exists_residual_plane_mover
    f hf hc hZ u hu huB huC hune
  have hgA : (g : G) ∈ normalizer (QuaternionSwapModel.A.map (movement r) : Set G) := by
    have hn := (QuaternionSwapModel.A.map f).le_normalizer_map Mc.subtype
      (mem_map_of_mem Mc.subtype hg)
    rw [map_map] at hn
    exact hn
  have hgV := source_movement_normalizer_control c r hgA
  have hVMc : markedPlane.map (movement r) ≤ Mc := by
    rintro _ ⟨q,hq,rfl⟩
    exact c.H_le_Mc (movement_mem r q).1
  apply hmove
  apply mem_normalizer_iff_map_conj_eq.mp
  rw [hmap,← subgroupOf_normalizer_eq hVMc]
  exact hgV

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
end

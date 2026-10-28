module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoProductLift

/-!
# Realizing the original Hall–Janko outer action in the concrete full Borel

The original Borel normalizes both reduced endpoints. Transporting this paired
action through the marked reduced isomorphism and applying the finite actor
recognition gives one involution in the actual outer Borel that agrees on both
whole endpoints. The same element agrees on every element of the reduced Borel.
The inverse transport retains the original conjugation maps literally.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–231.
This is the action input for the split extension comparison; the compatible
reduced isomorphism remains an earlier source input.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.ProductLift
open SuzukiContainment
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics

private theorem ambient_actor_lift
    {G : Type*} [Group G] (P B R : Subgroup G) (hP : B≤P) (hR : B≤R)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P B R hP hR) modelAmalgam)
    (x : G) (hxP : x∈normalizer (P:Set G)) (hxB : x∈normalizer (B:Set G))
    (hxR : x∈normalizer (R:Set G))
    (hk : x*(e.middle.symm sourceCartan:G)*x⁻¹=(e.middle.symm sourceCartan:G)⁻¹)
    (hd : x*(e.right.symm sourceCubic:G)=(e.right.symm sourceCubic:G)*x)
    (hz : x*(e.middle.symm sourceCentral:G)=(e.middle.symm sourceCentral:G)*x) :
    ∃ y : SecondParabolic.Overlap.outerB,
      y^2=1 ∧ (y:Extension)∉intoExtension.range ∧
      (∀ b : B, (e.middle (B.normalizerMonoidHom ⟨x,hxB⟩ b):Carrier)=
        extensionAction y (e.middle b:Carrier)) ∧
      (∀ v : P, (e.left (P.normalizerMonoidHom ⟨x,hxP⟩ v):Carrier)=
        extensionAction y (e.left v:Carrier)) ∧
      (∀ v : R, (e.right (R.normalizerMonoidHom ⟨x,hxR⟩ v):Carrier)=
        extensionAction y (e.right v:Carrier)) := by
  let b : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups P B R hP hR)
      (RankTwoAmalgam.ofSubgroups P B R hP hR) := {
    left := P.normalizerMonoidHom ⟨x,hxP⟩
    middle := B.normalizerMonoidHom ⟨x,hxB⟩
    right := R.normalizerMonoidHom ⟨x,hxR⟩
    left_commutes := fun _ => Subtype.ext rfl
    right_commutes := fun _ => Subtype.ext rfl }
  let a := (e.symm.trans b).trans e
  have hk' : a.middle sourceCartan=sourceCartan⁻¹ := by
    apply e.middle.symm.injective
    change e.middle.symm (e.middle (b.middle (e.middle.symm sourceCartan)))=_
    rw [e.middle.symm_apply_apply,map_inv]
    exact Subtype.ext hk
  have hd' : a.right sourceCubic=sourceCubic := by
    apply e.right.symm.injective
    change e.right.symm (e.right (b.right (e.right.symm sourceCubic)))=_
    rw [e.right.symm_apply_apply]
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr hd)
  have hz' : a.middle sourceCentral=sourceCentral := by
    apply e.middle.symm.injective
    change e.middle.symm (e.middle (b.middle (e.middle.symm sourceCentral)))=_
    rw [e.middle.symm_apply_apply]
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr hz)
  obtain ⟨y,hy,hyN,hB,hL,hR⟩ := model_actor_lift a hk' hd' hz'
  refine ⟨y,hy,hyN,?_,?_,?_⟩
  · intro v
    have hh := hB (e.middle v)
    change (e.middle (b.middle (e.middle.symm (e.middle v))):Carrier)=_ at hh
    rwa [e.middle.symm_apply_apply] at hh
  · intro v
    have hh := hL (e.left v)
    change (e.left (b.left (e.left.symm (e.left v))):Carrier)=_ at hh
    rwa [e.left.symm_apply_apply] at hh
  · intro v
    have hh := hR (e.right v)
    change (e.right (b.right (e.right.symm (e.right v))):Carrier)=_ at hh
    rwa [e.right.symm_apply_apply] at hh

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The same concrete outer involution induces both literal original endpoint
actions, and agrees on the full reduced Borel, in either orientation. -/
public theorem original_actor_lift
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)) modelAmalgam)
    (x : commonBorel L S)
    (hk : (x:G)*(e.middle.symm sourceCartan:G)*(x:G)⁻¹=(e.middle.symm sourceCartan:G)⁻¹)
    (hd : (x:G)*(e.right.symm sourceCubic:G)=(e.right.symm sourceCubic:G)*(x:G))
    (hz : (x:G)*(e.middle.symm sourceCentral:G)=(e.middle.symm sourceCentral:G)*(x:G)) :
    ∃ y : SecondParabolic.Overlap.outerB,
      y^2=1 ∧ (y:Extension)∉intoExtension.range ∧
      (∀ b : commonBorel L (reducedSylow L S),
        (e.middle ((commonBorel L (reducedSylow L S)).normalizerMonoidHom
          ⟨(x:G),borel_normalizes_reduced h x.property⟩ b):Carrier)=
          extensionAction y (e.middle b:Carrier)) ∧
      (∀ v : parabolic L (reducedSylow L S) i,
        (e.left (reducedEndpointAction h i x v):Carrier)=extensionAction y (e.left v:Carrier)) ∧
      (∀ v : parabolic L (reducedSylow L S) j,
        (e.right (reducedEndpointAction h j x v):Carrier)=extensionAction y (e.right v:Carrier)) := by
  exact ambient_actor_lift _ _ _ (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)
    e (x:G) (parabolic_normalizes_reduced h i (commonBorel_le_parabolic i x.property))
    (borel_normalizes_reduced h x.property)
    (parabolic_normalizes_reduced h j (commonBorel_le_parabolic j x.property)) hk hd hz

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.ProductLift

module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.Quotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SpecialGroup
public import Theory.Representation.PSL3Two.ParabolicCyclic
public import Theory.Representation.PSL3Two.SteinbergStructure.Duality

/-!
# Recognition transport for the original quotient in 14.7.72

An equivalence of the constructed S/V action with the actual Steinberg module
produces surjective coordinates with precisely V as kernel. If the point/line
marking first twists the actor, the automorphism invariance of Steinberg
removes that twist. Both constructions give equivariance under the original
qL and therefore apply to the proved center calculation.

The marked cyclic seed and the three-noncentral-chief-factor exclusion are
still needed to construct the representation equivalence. The transport
results below do not assert that missing recognition theorem.

Source: Aschbacher–Smith, proof of 14.7.72, printed p.1076 (PDF p.1093),
using H.6.5 and 14.7.22(2), manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  [(V.subgroupOf (S F L)).Normal]
  [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))]

/-- Compose a genuine quotient equivalence with the literal S → S/V map. -/
noncomputable def QuotientAction.steinbergCoordinates (a : QuotientAction d)
    (e : a.representation.Equiv BinaryLinearThree.S) : SteinbergCoordinates d where
  coordinates :=
    (AddMonoidHom.toMultiplicative e.toLinearEquiv.toLinearMap.toAddMonoidHom).comp
      quotientCoordinates
  onto := by
    intro v
    obtain ⟨x, hx⟩ := e.toLinearEquiv.surjective v.toAdd
    obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective (V.subgroupOf (S F L)) x.toMul
    refine ⟨s, ?_⟩
    change e (Additive.ofMul (QuotientGroup.mk' _ s)) = v.toAdd
    rw [hs]
    exact hx
  kernel_eq := by
    ext s
    change e.toLinearEquiv (quotientCoordinates s).toAdd = 0 ↔ (s : G) ∈ V
    rw [← e.toLinearEquiv.map_zero, e.toLinearEquiv.injective.eq_iff]
    exact QuotientGroup.eq_one_iff s
  equivariant := by
    intro l s
    change e (quotientCoordinates _).toAdd =
      BinaryLinearThree.S (d.qL l) (e (quotientCoordinates s).toAdd)
    rw [a.equivariant]
    exact IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap _ _

/-- Remove any explicit change of actor marking, including point/line duality. -/
noncomputable def QuotientAction.untwist (a : QuotientAction d)
    (σ : MulAut BinaryLinearThree.Group)
    (e : Representation.Equiv (a.representation.comp σ.toMonoidHom) BinaryLinearThree.S) :
    a.representation.Equiv BinaryLinearThree.S := by
  let e' : a.representation.Equiv
      (BinaryLinearThree.S.comp σ.symm.toMonoidHom) := .mk e.toLinearEquiv (by
    intro g
    rw [e.toLinearEquiv_toLinearMap]
    have he := e.toIntertwiningMap.isIntertwining' (σ.symm g)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using he)
  exact e'.trans (BinaryLinearThree.SteinbergStructure.autEquiv σ.symm).symm

/-- The coordinates retain qL after recognition in a different parabolic marking. -/
noncomputable def QuotientAction.steinbergCoordinatesOfTwist (a : QuotientAction d)
    (σ : MulAut BinaryLinearThree.Group)
    (e : Representation.Equiv (a.representation.comp σ.toMonoidHom) BinaryLinearThree.S) :
    SteinbergCoordinates d :=
  a.steinbergCoordinates d (a.untwist d σ e)

/-- Actual application of the quotient construction and recognition transport:
the original center theorem needs no actor-containment assumption. -/
theorem center_eq_of_quotient_equiv
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcomm : ⁅S F L, Q T L⁆ ≤ V)
    (hcentral : V ≤ (center (S F L)).map (S F L).subtype)
    (hderived : ⁅S F L, S F L⁆ = V)
    (e : (quotientAction d hTL hcomm).representation.Equiv BinaryLinearThree.S) :
    (center (S F L)).map (S F L).subtype = V :=
  center_eq_of_steinberg d ((quotientAction d hTL hcomm).steinbergCoordinates d e)
    hcentral hderived

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition

module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SourceDistanceFourNatural
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SourceDistanceFourSections
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.Input
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DoubleDualQuotient

/-!
# Excluding distance four for the original pure-point residual

The actual residual core maps onto the point radical and contains the original
natural four-space. Its central quotient therefore has opposing natural and
dual three-dimensional sections. The genuine nonabelian distance-four source
instead makes that quotient a homogeneous irreducible double, which is
impossible. Both sections retain the same original residual actor; no
compatibility between independently chosen quotient markings is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open ChapterC ChapterC.BinaryMS ChapterC.BinaryMS.MS93
open BinaryLinear BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The central quotient of the original point-residual core cannot be the
homogeneous double supplied by the distance-four source. -/
theorem pure_not_naturalCenterDoubleDualQuotient
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (q : NaturalCenterDoubleDualQuotient
      ((B.pointResidual w).subgroupOf (B.pointResidual w ⊔ B.pointSylow w))) : False := by
  let X := B.pointResidual w
  let K := X.subgroupOf (X ⊔ B.pointSylow w)
  let eK : K ≃* X := subgroupOfEquivOfLe (show X ≤ X ⊔ B.pointSylow w from le_sup_left)
  have hmap : (blockU K).map eK.toMonoidHom = blockU X := by
    rw [blockU, map_commutator, pCore_map_iso,
      map_top_of_surjective _ eK.surjective]
    rfl
  let F : blockU K ≃* blockU X :=
    (eK.subgroupMap (blockU K)).trans (MulEquiv.subgroupCongr hmap)
  have hF (k : K) (a : blockU K) :
      F (MulAut.conjNormal k a) = MulAut.conjNormal (eK k) (F a) := by
    apply Subtype.ext
    change eK (k * a.val * k⁻¹) = eK k * eK a.val * (eK k)⁻¹
    simp only [map_mul, map_inv]
  let f := (S.distanceFourPointAction w hw hp).comp eK.toMonoidHom
  let r := (S.distanceFourBlockActor w hw hp).comp F.toMonoidHom
  have hr (a : blockU K) : (r a).val = f a.val := rfl
  let i := F.symm.toMonoidHom.comp (S.distanceFourNaturalIntoBlock hNM w hw hp)
  have hi : Function.Injective i :=
    F.symm.injective.comp (S.distanceFourNaturalIntoBlock_injective hNM w hw hp)
  have he (k : K) (v : Space 4) :
      MulAut.conjNormal k (i (Multiplicative.ofAdd v)) =
        i (Multiplicative.ofAdd ((f k).val v)) := by
    apply F.injective
    rw [hF]
    change MulAut.conjNormal (eK k)
        (F (F.symm (S.distanceFourNaturalIntoBlock hNM w hw hp (Multiplicative.ofAdd v)))) =
      F (F.symm (S.distanceFourNaturalIntoBlock hNM w hw hp
        (Multiplicative.ofAdd ((f k).val v))))
    rw [F.apply_symm_apply, F.apply_symm_apply]
    exact S.distanceFourNaturalIntoBlock_equivariant hNM w hw hp (eK k) v
  let E : (blockU K ⧸ center (blockU K)) ≃*
      Multiplicative (MS93.DistanceFour.Linear.W × MS93.DistanceFour.Linear.W) :=
    (QuotientGroup.quotientMulEquivOfEq q.kernel.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q.quotient q.onto)
  have hE (a : blockU K) : E (QuotientGroup.mk' _ a) = q.quotient a := rfl
  let mark : K →* BinaryLinearThree.Group :=
    q.marking.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let b := BinaryLinearThree.AutomorphismAction.graph.toMonoidHom.comp mark
  let σ := BinaryLinearThree.W.comp b
  have hb : Function.Surjective b := BinaryLinearThree.AutomorphismAction.graph.surjective.comp
    (q.marking.surjective.comp (QuotientGroup.mk'_surjective _))
  let : IsIrreducible σ := (irreducible_comp_surjective_iff b hb BinaryLinearThree.W).mpr
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  have hact (k : K) (z : blockU K ⧸ center (blockU K)) :
      (E (SourceDistanceFourSections.centralAction (blockU K) k z)).toAdd =
        (σ k (E z).toAdd.1, σ k (E z).toAdd.2) := by
    induction z using Quotient.inductionOn with
    | h a =>
      change (E (SourceDistanceFourSections.centralAction (blockU K) k
        (QuotientGroup.mk' _ a))).toAdd = _
      rw [SourceDistanceFourSections.centralAction_mk, hE]
      change (q.quotient (blockConjugate K k a)).toAdd = _
      exact q.quotient_action k a
  exact SourceDistanceFourSections.not_homogeneous_double
    (blockU K) f r hr i he (S.distanceFourPointVector_ne_zero w hw hp)
    ((S.distanceFourPointAction_surjective w hw hp).comp eK.surjective)
    ((S.distanceFourBlockActor_surjective w hw hp).comp F.surjective) hi σ E hact

include S in
/-- The literal pure-point binary MS setup cannot have critical distance four. -/
theorem pure_binary_setup_distance_ne_four
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (hms : SmallMSPair KnownSimple.IsKnownSimple (B.pointResidual w) (B.pointSylow w))
    (e : (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : InputSetup (hms.binaryInput e))
    (hc : ¬ IsMulCommutative (commutatorCore
      ((B.pointResidual w).subgroupOf (B.pointResidual w ⊔ B.pointSylow w)))) :
    t.geometry.b t.reduction.radical ≠ 4 := by
  intro hb
  obtain ⟨q⟩ := t.naturalCenterDoubleDualQuotient_of_nonabelian_distance_four hc hb
  exact S.pure_not_naturalCenterDoubleDualQuotient hNM w hw hp q

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

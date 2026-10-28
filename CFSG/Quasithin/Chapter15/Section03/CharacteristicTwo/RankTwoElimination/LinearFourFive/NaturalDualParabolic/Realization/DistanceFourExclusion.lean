module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ResidualStructure.ResidualQuotientGeometry.BinaryInput
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DoubleDualQuotient
public import Theory.Representation.PSL3Two.HomogeneousDouble.GroupSections
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.AbelianExclusion

/-!
# Excluding distance four for the actual natural-dual residual

The source distance-four core modulo its full center is a homogeneous double
of an irreducible three-dimensional module. The actual residual core has a
natural three-space embedded in this quotient and a dual three-space as its
quotient, under the same surjective residual actor. Schur's lemma would make
these two opposing modules equivalent, contradicting their explicit binary
natural/dual inequivalence. No agreement between the source's marking and the
residual's marking is required.

The final Sylow/theta consumer supplies the geometric placement and excludes
the abelian case, so the original source24 input is reduced to critical distance
greater than four. Its larger-distance path geometry remains a separate source
obligation; this module does not assert the full C.1.34 classification.

Source: Aschbacher--Smith 15.3.24, printed pp.1129--1130, and
Meierfrankenfeld--Stellmacher (1993), (4.6.12), pp.910--912.
-/

@[expose] public noncomputable section
open Subgroup BinaryLinear.OuterCyclic Representation
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open Theory.LinearAlgebra.BinaryFivePointStabilizer
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
open ChapterC ChapterC.BinaryMS ChiefLayers
universe u
variable {G : Type u} [Group G] [Finite G] {d : LocalData G} {L : Subgroup G}

/-- The actual residual central quotient has opposing natural and dual
factors, so cannot be the source's homogeneous double. -/
theorem not_naturalCenterDoubleDualQuotient {κ : GroupClass.{u}}
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (input : Input κ (residualComponent h x) (sylowPart h x))
    (q : NaturalCenterDoubleDualQuotient (residualComponent h x)) : False := by
  let F : blockU (residualComponent h x) ≃* residualCore h x :=
    input.intrinsicCoreEquiv.trans (binaryInputResidualCoreEquiv h x input)
  let f := q.quotient.comp F.symm.toMonoidHom
  have hf : f.ker = center (residualCore h x) := by
    rw [← MonoidHom.comap_ker, q.kernel]
    ext k
    change F.symm k ∈ center (blockU (residualComponent h x)) ↔ k ∈ center (residualCore h x)
    constructor
    · intro hk
      have he := (centerCongr F ⟨F.symm k,hk⟩).property
      change F (F.symm k) ∈ _ at he
      simpa only [F.apply_symm_apply] using he
    · intro hk
      exact (centerCongr F.symm ⟨k,hk⟩).property
  let E : (residualCore h x ⧸ center (residualCore h x)) ≃*
      Multiplicative (MS93.DistanceFour.Linear.W × MS93.DistanceFour.Linear.W) :=
    (QuotientGroup.quotientMulEquivOfEq hf.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f (q.onto.comp F.symm.surjective))
  have hEF (b : blockU (residualComponent h x)) :
      E (QuotientGroup.mk' _ (F b)) = q.quotient b := by
    change q.quotient (F.symm (F b)) = _
    rw [F.symm_apply_apply]
  let lD : residualComponent h x ≃* Stellmacher.twoResidualAmbient (point h x) :=
    subgroupOfEquivOfLe (show Stellmacher.twoResidualAmbient (point h x) ≤
      residualOvergroup h x from le_sup_left)
  let lP : residualComponent h x →* point h x :=
    (residualPointInclusion h hx).comp lD.toMonoidHom
  let a : residualComponent h x →* BinaryLinear.GL (pointQuotient x) :=
    (residualQuotientActor h hx).comp lD.toMonoidHom
  have ha : Function.Surjective a :=
    (residualQuotientActor_surjective h hx).comp lD.surjective
  let mark : residualComponent h x →* BinaryLinearThree.Group :=
    q.marking.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (residualComponent h x)))
  let b := BinaryLinearThree.AutomorphismAction.graph.toMonoidHom.comp mark
  let σ := BinaryLinearThree.W.comp b
  have hb : Function.Surjective b := BinaryLinearThree.AutomorphismAction.graph.surjective.comp
    (q.marking.surjective.comp (QuotientGroup.mk'_surjective _))
  let : IsIrreducible σ := (irreducible_comp_surjective_iff b hb BinaryLinearThree.W).mpr
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let act := (residualCentralActor h hx).comp lP
  have hact (l : residualComponent h x) (z : residualCore h x ⧸ center (residualCore h x)) :
      (E (act l z)).toAdd = (σ l (E z).toAdd.1, σ l (E z).toAdd.2) := by
    induction z using Quotient.inductionOn with
    | h k =>
      obtain ⟨t,rfl⟩ := F.surjective k
      change (E (residualCentralActor h hx (lP l) (QuotientGroup.mk' _ (F t)))).toAdd = _
      rw [residualCentralActor_mk]
      have hcon : conjugate _ _ (residualCore_normalized h hx) (lP l) (F t) =
          F (blockConjugate (residualComponent h x) l t) := by
        apply Subtype.ext
        change (l.val.val:G) * (t.val.val.val:G) * (l.val.val:G)⁻¹ = _
        rfl
      rw [hcon,hEF]
      have hEF' : E ⟦F t⟧ = q.quotient t := hEF t
      rw [hEF']
      exact q.quotient_action l t
  exact BinaryLinearThree.HomogeneousDouble.no_opposing_group_sections
    a ha (quotientCoordinates hx) σ act E hact
    (naturalIntoResidualCentral h hx hU) (naturalIntoResidualCentral_injective h hx hU)
    (fun l w => naturalIntoResidualCentral_equivariant h hx hU (lP l) w)
    (residualCentralDualProjection h hx hU) (residualCentralDualProjection_surjective h hx hU)
    (fun l z => residualCentralDualProjection_equivariant h hx hU (lP l) z)

/-- The original source construction excludes distance four for the actual
residual input, without a full C.1.34 alternatives premise. -/
theorem binaryInput_distance_ne_four {κ : GroupClass.{u}}
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (input : Input κ (residualComponent h x) (sylowPart h x))
    (s : MS93.InputSetup input)
    (hc : ¬ IsMulCommutative (commutatorCore (residualComponent h x))) :
    s.geometry.b s.reduction.radical ≠ 4 := by
  intro hb
  obtain ⟨q⟩ := s.naturalCenterDoubleDualQuotient_of_nonabelian_distance_four hc hb
  exact not_naturalCenterDoubleDualQuotient h hx hU input q

/-- The original Sylow/theta hypotheses eliminate the abelian and distance-four
branches. Every actual residual source setup has distance greater than four. -/
theorem binaryInput_distance_gt_four_of_theta {κ : GroupClass.{u}}
    [IsElementaryAbelian 2 (d.componentSpan L)] {I : Subgroup G}
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (input : Input κ (residualComponent h x) (sylowPart h x))
    (s : MS93.InputSetup input) : 4 < s.geometry.b s.reduction.radical := by
  have hc := binaryInput_core_nonabelian_of_theta h hx hS hθ input
  have hne := binaryInput_distance_ne_four h hx
    ((spanCommutator_le_componentCore_of_theta hS hθ).trans (componentCore_le_pointCore h x))
    input s hc
  obtain ⟨common⟩ := s.commonFacts hc
  have hlarge := common.large_distance
  obtain ⟨n, hn⟩ := s.geometry.even
    (MS93.alpha s.reduction.radical) rfl
  change s.geometry.b s.reduction.radical = n + n at hn
  omega

/-- The actual source24 input produces a large-distance source setup. Its
remaining path-centrality obligation belongs to the larger-distance branch. -/
theorem binaryInput_exists_large_distance_of_theta {κ : GroupClass.{u}}
    [IsElementaryAbelian 2 (d.componentSpan L)] {I : Subgroup G}
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (input : Input κ (residualComponent h x) (sylowPart h x)) :
    ∃ s : MS93.InputSetup input, 4 < s.geometry.b s.reduction.radical := by
  obtain ⟨s⟩ := MS93.exists_setup input
    (binaryInput_core_nonabelian_of_theta h hx hS hθ input)
  exact ⟨s,binaryInput_distance_gt_four_of_theta h hx hS hθ input s⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization

module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourBlock
public import Theory.SpecificGroups.PSL3Four.CentralCover.CoreCommutatorQuotient
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourBlock

/-!
# The actual Hermitian central cover L/V

The original core commutator and block kernel identify the quotient map to
PSL₃(4). Its factor through L/V is a perfect central cover with kernel exactly
O₂(L)/V, which is elementary abelian. I.2.2(3b) now supplies core commutator
generation in both original parabolic preimages and their solvable residuals,
modulo the full original V.

The internal block import reuses the checked original component-kernel proof.
No assertion that this central kernel is trivial is made here; its exclusion
still needs the selected pair's module structure.
Source: Aschbacher–Smith 8.2.10(3), printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The original component map, in the native projective field-four coordinates. -/
@[expose] def hermitianFieldFourProjection
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1))) : L →* Matrix.PSL3Four.PSL :=
  (((binaryImageEquiv 1).symm.trans (imageEquivPSL 1 (by decide))).trans
    (Matrix.PSL3.ExceptionalFourCover.baseEquiv (E 1) (by rw [card_E]; norm_num)).symm).toMonoidHom.comp
      (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom)

/-- The actual quotient L/V, its full central kernel, and the lifted parabolic
commutators. The original component homomorphism is retained on representatives. -/
theorem sourceOrbit_hermitian_central_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hcomm : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit)
    (hcommL : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1))) :
    let W := D.sourceOrbit.subgroupOf L
    let f := D.hermitianFieldFourProjection d
    Group.IsPerfect L ∧ IsElementaryAbelian 2 (pCore 2 L) ∧
      Function.Surjective f ∧ f.ker = pCore 2 L ∧
      ∃ hW : W.Normal, letI := hW
        IsQuasisimple (L ⧸ W) ∧
        center (L ⧸ W) = (pCore 2 L).map (QuotientGroup.mk' W) ∧
        IsElementaryAbelian 2 (center (L ⧸ W)) ∧
        ∃ c : PerfectCentralCovering.Cover (L ⧸ W) Matrix.PSL3Four.PSL,
          (∀ l : L, c.toMonoidHom (QuotientGroup.mk' W l) = f l) ∧
          c.toMonoidHom.ker = (pCore 2 L).map (QuotientGroup.mk' W) ∧
          ∀ b : Bool, let P := Matrix.PSL3Four.ElementaryParabolic.liftedParabolic f b
            ⁅P.pCoreIn 2,P⁆ ⊔ W = P.pCoreIn 2 ∧
              (⁅(solvableResidual P).pCoreIn 2,solvableResidual P⁆).map P.subtype ⊔ W =
                P.pCoreIn 2 := by
  let W := D.sourceOrbit.subgroupOf L
  let f := D.hermitianFieldFourProjection d
  let e := ((binaryImageEquiv 1).symm.trans (imageEquivPSL 1 (by decide))).trans
    (Matrix.PSL3.ExceptionalFourCover.baseEquiv (E 1) (by rw [card_E]; norm_num)).symm
  have hf : Function.Surjective f := e.surjective.comp
    (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective)
  have hk : f.ker = pCore 2 L := by
    rw [show f = e.toMonoidHom.comp (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom) from rfl,
      MonoidHom.ker_comp_of_injective _ _ e.injective,
      MonoidHom.ker_comp_of_injective _ _ d.groupEquiv.injective]
    exact D.hermitian_component_kernel h hmany hV hnon hcommL 1 d
  let hW : W.Normal := normal_subgroupOf_of_le_normalizer D.sourceOrbit_component_normalizes
  let := hW
  have hWL : D.sourceOrbit ≤ L := hV ▸ D.le_component
  have hcomm' : ⁅pCore 2 L,(⊤ : Subgroup L)⁆ = W := by
    apply map_injective L.subtype_injective
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hWL]
    exact hcommL
  have hWC : W ≤ pCore 2 L := hcomm'.ge.trans (commutator_le_left _ _)
  let K := L.subgroupOf (L ⊔ (T : Subgroup G))
  let : Group.IsPerfect K := h.maximal_faithful.1.1.1.perfect
  let eK : K ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := eK.toMonoidHom) eK.surjective
  let : IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) :=
    D.sourceOrbit_elementary_join_core_of_core_commutator h hmany hV hnon hcomm
  have hLQ : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer D.sylow_normalizes_component)
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.of_le hLQ
  let : IsElementaryAbelian 2 ((pCore 2 L).map L.subtype) :=
    show IsElementaryAbelian 2 (L.pCoreIn 2) from inferInstance
  let eC := (pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective
  let : IsElementaryAbelian 2 (pCore 2 L) :=
    IsElementaryAbelian.of_injective eC.toMonoidHom eC.injective
  let : IsSimpleGroup Matrix.PSL3Four.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let c := CoreCommutatorCover.cover W f hf hWC hk hcomm'.le
  have hz : center (L ⧸ W) = (pCore 2 L).map (QuotientGroup.mk' W) :=
    CoreCommutatorCover.center_eq_core_image W f hf hWC hk hcomm'.le
  have hzE : IsElementaryAbelian 2 (center (L ⧸ W)) := hz.symm ▸ IsElementaryAbelian.map _
  refine ⟨inferInstance,inferInstance,hf,hk,hW,c.isQuasisimple,hz,hzE,c,?_,
    by rw [CoreCommutatorCover.cover_toMonoidHom]; exact CoreCommutatorCover.projection_ker W f hWC hk,?_⟩
  · intro l
    rw [CoreCommutatorCover.cover_toMonoidHom]
    exact CoreCommutatorCover.projection_mk W f hWC hk l
  · exact Matrix.PSL3Four.ElementaryParabolic.lifted_parabolic_core_structure
      W f hf hWC hk hcomm'.le

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

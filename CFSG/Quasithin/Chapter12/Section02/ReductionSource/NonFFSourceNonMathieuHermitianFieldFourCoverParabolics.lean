module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourCentralCover
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCoverMarking
public import Theory.GroupTheory.AmalgamLocalCores
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates

/-!
# Central-cover commutators at the original selected four-space

The selected four-space is the corner space after a literal inner change of
Hermitian coordinates. Its normalizer inside L is therefore exactly the native
line-parabolic preimage. Transporting the central-cover core calculation through
that marking gives [O₂(P),P]V = O₂(P) and [O₂(R),R]V = O₂(P), for
P = N_L(U) and its actual solvable residual R. In particular O₂(L) lies in
[O₂(R),R]V. The full central kernel O₂(L)/V is retained.

The internal coordinate import supplies the original action on representatives.
Source: Aschbacher–Smith 8.2.10(3), printed p.721, using I.2.2(3b),
refs/quasithin.pdf. Its remaining kernel-exclusion step uses the selected pair.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- Both original parabolic commutators, at the literal selected four-space. -/
theorem sourceOrbit_hermitian_selected_cover_parabolics
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hcomm : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit)
    (hcommL : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) :
    let U := D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
    let P := L ⊓ normalizer (U : Set G)
    let R := Chapter8.Section02.Normalizer.localResidual L U
    ⁅P.pCoreIn 2,P⁆ ⊔ D.sourceOrbit = P.pCoreIn 2 ∧
      ⁅R.pCoreIn 2,R⁆ ⊔ D.sourceOrbit = P.pCoreIn 2 ∧
      L.pCoreIn 2 ≤ ⁅R.pCoreIn 2,R⁆ ⊔ D.sourceOrbit := by
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let P := L ⊓ normalizer (U : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let W := D.sourceOrbit.subgroupOf L
  obtain ⟨hperfect,helem,_,hk,hW,_⟩ :=
    D.sourceOrbit_hermitian_central_cover h hmany hV hnon hcomm hcommL d
  let : Group.IsPerfect L := hperfect
  let : IsElementaryAbelian 2 (pCore 2 L) := helem
  let : W.Normal := hW
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨c,hU,_⟩ := selected_one_section_coordinates s D.sourceOrbit_weakClosure_setup
    (D.hermitianOrbitCoordinates 1 d) j hj he
  let z := binaryActionHom 1 c
  let z' : binaryImage 1 := ⟨z,⟨c,rfl⟩⟩
  let e := (D.hermitianOrbitCoordinates 1 d).trans z
  let a := d.groupEquiv.toMonoidHom.comp D.orbitComponentHom
  let q := (MulAut.conj z').toMonoidHom.comp a
  let f := nativeBinaryEquiv.symm.toMonoidHom.comp q
  have hf : Function.Surjective f := nativeBinaryEquiv.symm.surjective.comp
    ((MulAut.conj z').surjective.comp (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective))
  have hfk : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ nativeBinaryEquiv.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z').injective]
    change (nativeBinaryEquiv.symm.toMonoidHom.comp a).ker = pCore 2 L at hk
    rwa [MonoidHom.ker_comp_of_injective _ _ nativeBinaryEquiv.symm.injective] at hk
  have heq (l : L) (v : Additive D.sourceOrbit) :
      e (automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) v) = (q l).val (e v) := by
    change z (D.hermitianOrbitCoordinates 1 d
      (automizerRepresentation D.sourceOrbit (D.hermitianComponentAutomizer l) v)) =
        z ((d.groupEquiv (D.orbitComponentHom l)).val
          (z.symm (z (D.hermitianOrbitCoordinates 1 d v))))
    exact (congrArg z (D.hermitianOrbitCoordinates_component 1 d l v)).trans
      (congrArg (fun w => z ((d.groupEquiv (D.orbitComponentHom l)).val w))
        (z.symm_apply_apply (D.hermitianOrbitCoordinates 1 d v)).symm)
  let P₀ := Matrix.PSL3Four.ElementaryParabolic.liftedParabolic f false
  have hP₀ : P₀ = (normalizer (U : Set G)).subgroupOf L :=
    marked_corner_normalizer_preimage D.sourceOrbit L U inf_le_left
      D.sourceOrbit_component_normalizes e q heq hU
  have hPmap : P₀.map L.subtype = P := by
    rw [hP₀,subgroupOf_map_subtype,inf_comm]
  have hWL : D.sourceOrbit ≤ L := hV ▸ D.le_component
  have hcomm' : ⁅pCore 2 L,(⊤ : Subgroup L)⁆ = W := by
    apply map_injective L.subtype_injective
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype,map_subgroupOf_eq_of_le hWL]
    exact hcommL
  have hWC : W ≤ pCore 2 L := hcomm'.ge.trans (commutator_le_left _ _)
  obtain ⟨hP,hR⟩ := Matrix.PSL3Four.ElementaryParabolic.lifted_parabolic_core_structure
    W f hf hWC hfk hcomm'.le false
  have hRmap : (solvableResidual P₀).map (L.subtype.comp P₀.subtype) = R := by
    let eP : P₀ ≃* P := (P₀.equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hPmap)
    have hm := congrArg (Subgroup.map P.subtype)
      (map_solvableResidual_eq eP.toMonoidHom eP.surjective)
    rw [map_map] at hm
    exact hm
  have hP' := congrArg (Subgroup.map L.subtype) hP
  rw [Subgroup.map_sup,map_commutator,
    ←AmalgamLocalCores.pCoreIn_map_of_injective 2 L.subtype L.subtype_injective,
    hPmap,map_subgroupOf_eq_of_le hWL] at hP'
  have hR' := congrArg (Subgroup.map L.subtype) hR
  rw [Subgroup.map_sup,map_map,map_commutator,
    ←AmalgamLocalCores.pCoreIn_map_of_injective 2 (L.subtype.comp P₀.subtype)
      (L.subtype_injective.comp P₀.subtype_injective),hRmap,
    map_subgroupOf_eq_of_le hWL,
    ←AmalgamLocalCores.pCoreIn_map_of_injective 2 L.subtype L.subtype_injective,hPmap] at hR'
  have hQC : L.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
    rw [←hV]
    exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hQP : L.pCoreIn 2 ≤ P := le_inf (pCoreIn_le 2 L)
    ((hQC.trans (centralizer_le (show U ≤ D.sourceOrbit from inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _))
  have hQPC : L.pCoreIn 2 ≤ P.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 L) hQP
    (inf_le_left.trans (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))))
  exact ⟨hP',hR',hQPC.trans hR'.ge⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.JoinSelection
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.Join.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.Maximality
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Source

/-!
# Original generated seven-letter block reconstruction

The original d and I determine every subgroup. The established generated
component theorem supplies C = O²(I₀), the first radical and the Sylow
supplement. Maximal intersection excludes the normal Baumann alternative,
and the full B.5 star action feeds whole-block selection on CR₁.

The normal extension of the full moved action proves CR₁ = I₀: the
faithful actor is already filled by CR₁, and its kernel lies in O₂(I₀) ≤ R₁.
This discharges the join premise and reconstructs the original whole block
without additional action, shortness or classification assumptions. The
seven-letter source application retains only the separately owned ordinary
and exceptional geometry inputs.

Source: Aschbacher--Smith, 14.6.10(5), pp.1029--1030.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Every source and selection premise except the residual-join bridge is
discharged for the unchanged generated component. -/
theorem reconstructionInput_of_residualJoin (hj : ResidualJoinInput (G := G)) :
    ReconstructionInput hG T hempty hM hunique hmany hcard e hab := by
  intro H hH d I hI he
  obtain ⟨eC⟩ := he
  let I0 := sourceGeneratedParabolic T M Mc I d.H2
  let C := sourceGeneratedComponent T M Mc I d.H2
  let I1 := firstResidual T M Mc I d.H2 ⊔ ((T : Subgroup G) ⊓ I0)
  let R := I1.pCoreIn 2
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hout := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨hI0,_,_⟩ := source_generated_parabolic_cores_of_marked_recognition
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal
    ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
    ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput
    I d.H2 hI hout d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  obtain ⟨K,_,_,_,_,hK,hsup,_⟩ := source_generated_parabolic_module_data
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  subst K
  have hms := generated_ms_inputs hG T hempty hM hunique hmany hcard e hab H hH d I hI
  have hi : Input KnownSimple.IsKnownSimple I0 R (I0 ⊓ M) C := hms.1
  obtain ⟨m⟩ := star_actionData hi eC
  have hjoin : I0 = C ⊔ R := hj I0 C R (I0 ⊓ M) hi rfl hms.2.1 eC m
  have hSyl := source_suitable_intersection_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.index d.moves_core d.product_moves_core d.local_normalizer hlocal
    I0 hI0.1
  obtain ⟨P,hP⟩ := hSyl.1
  let : (C.subgroupOf I0).Normal := by
    change (((pResidual 2 I0).map I0.subtype).comap I0.subtype).Normal
    rw [comap_map_eq_self_of_injective I0.subtype_injective]
    infer_instance
  have hgen : C.subgroupOf I0 ⊔ (P : Subgroup I0) = ⊤ := by
    apply map_injective I0.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hi.component.1,hP,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hsup
  have hprod : ∀ g : I0, ∃ k ∈ C.subgroupOf I0, ∃ t ∈ (P : Subgroup I0), k*t=g := by
    intro g
    exact mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top g)
  exact block_types_of_join_eq hi hjoin eC P hprod
    (no_normal_characteristic_baumann T _ M Mc I0 hI0 hSyl.2 P hP)

/-- Whole-block reconstruction for the original generated component, with
the residual–radical generation premise discharged. -/
theorem reconstructionInput :
    ReconstructionInput hG T hempty hM hunique hmany hcard e hab :=
  reconstructionInput_of_residualJoin hG T hempty hM hunique hmany hcard e hab
    residualJoinInput

/-- Application to the existing seven-letter assembly. The ordinary and
exceptional geometry have independent owners. -/
theorem source_branch_of_residualJoin
    (hj : ResidualJoinInput (G := G))
    (ho : OrdinaryGeometryInput hG T hempty hM hunique hmany hcard e hab)
    (hx : ExceptionalRankInput hG T hempty hM hunique hmany hcard e hab) :
    SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))) :=
  source_branch_of_inputs hG T hempty hM hunique hmany hcard e hab
    (reconstructionInput_of_residualJoin hG T hempty hM hunique hmany hcard e hab hj) ho hx

/-- The actual seven-letter source consumer with reconstruction discharged.
Only the independent ordinary and exceptional geometry inputs remain. -/
theorem source_branch_of_geometry
    (ho : OrdinaryGeometryInput hG T hempty hM hunique hmany hcard e hab)
    (hx : ExceptionalRankInput hG T hempty hM hunique hmany hcard e hab) :
    SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))) :=
  source_branch_of_inputs hG T hempty hM hunique hmany hcard e hab
    (reconstructionInput hG T hempty hM hunique hmany hcard e hab) ho hx

end CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction

module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveQuotient
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralCubicExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaWreathExclusion

/-!
# The actual wreath local forces the marked order-five source configuration

The proved Omega and cubic obstructions eliminate those two original action
rows. In the remaining dihedral row the literal marking has p=5 and m=2.
Its source residual generates V from the original central seed, moves all
of V, and has YT as a uniqueness subgroup. Its nontrivial two-core and
both residual normalizers remain in the selected M. The original Rc is
Sylow in YRc, whose quotient by its two-core is D₁₀ or the actual Sz(2).

This is the front reduction of original15.2.4. The later mixed D10/Sz(2)
and A5 amalgam contradiction is a separate proof obligation; no hypothesis
asserting that contradiction is inserted into this theorem.

Source: Aschbacher--Smith15.2.4, printed pp.1105--1107.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- A literal symmetric-five wreath H-star forces the exact marked five residual setup. -/
theorem source_HStar_wreath_five_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let ρ := imageRepresentation M V hV.normalized
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    ∃ l : LocalGeneration (ρ.comp (Jhat ρ).subtype),
      DihedralMarking l 5 2 ∧
      V = conjugateSpanBy (centralInvolutions T ⊓ V) Y ∧
      maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) = {M} ∧
      ⁅V,Y⁆ = V ∧ V ≤ Y.pCoreIn 2 ∧
      normalizer (Y.pCoreIn 2 : Set G) ≤ M ∧ normalizer (Y : Set G) ≤ M := by
  have hD := hcases.resolve_right (fun ho =>
    source_omega_chosen_HStar_not_symmetricFive_wreath hG T hempty hM hJ hu hmany hV ho hH he)
  obtain ⟨l,p,m,hp,hd⟩ := hD
  rcases (primeDimensionOptions_iff p m).mp hp with ⟨rfl,_⟩ | ⟨rfl,rfl⟩
  · exact (source_dihedral_cubic_HStar_not_symmetricFive_wreath
      hG T hempty hM hJ hu hmany hV l hp hd hH he).elim
  · exact ⟨l,hd,
      source_dihedral_five_residual_seed_span hG T hempty hM hJ hu hmany hV l hp hd,
      source_dihedral_five_residual_sylow_unique hG T hempty hM hJ hu hmany hV l hp hd,
      source_dihedral_five_residual_movement hG T hempty hM hJ hu hmany hV l hp hd,
      source_dihedral_five_residual_core_normalizer hG T hempty hM hJ hu hmany hV l hp hd⟩

/-- The same literal wreath assumption supplies the residual two-core and Rc Sylow facts. -/
theorem source_HStar_wreath_five_core_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let ρ := imageRepresentation M V hV.normalized
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let R := (M ⊓ Mc).pCoreIn 2
    ∃ l : LocalGeneration (ρ.comp (Jhat ρ).subtype),
      DihedralMarking l 5 2 ∧ (pCore 2 Y).index = 5 ∧ Y.pCoreIn 2 ≤ M.pCoreIn 2 ∧
      ∃ S : Sylow 2 ↑(Y ⊔ R), (S : Subgroup ↑(Y ⊔ R)).map (Y ⊔ R).subtype = R := by
  obtain ⟨l,hd,_⟩ := source_HStar_wreath_five_reduction
    hG T hempty hM hJ hu hmany hV hcases hH he
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨hi,hcore⟩ := source_dihedral_five_residual_core_index hG T hempty hM hJ hu hmany hV l hp hd
  exact ⟨l,hd,hi,hcore,
    source_dihedral_five_intersection_core_sylow hG T hempty hM hJ hu hmany hV l hp hd⟩

/-- The actual wreath local forces the source residual join into the two mixed rank-one models. -/
theorem source_HStar_wreath_residual_join_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let L := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
      (M ⊓ Mc).pCoreIn 2
    Nonempty ((L ⧸ pCore 2 L) ≃* DihedralGroup 5) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  obtain ⟨l,hd,_⟩ := source_HStar_wreath_five_reduction
    hG T hempty hM hJ hu hmany hV hcases hH he
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  exact source_dihedral_five_join_quotient hG T hempty hM hJ hu hmany hV l hp hd

end CFSG.Quasithin.Chapter15.Section02

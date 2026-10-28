module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveReduction
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.ChosenResidualNormalizer
public import CFSG.Quasithin.Chapter15.Section01.WreathFactor
public import CFSG.Quasithin.Chapter15.Section01.WreathCore

/-!
# The literal mixed rank-one configuration forced by a wreath local

The actual H-star wreath assumption forces the marked five residual. Its
intersection core Rc is Sylow in L₀=YRc and L₀/O₂(L₀) is D₁₀ or Sz(2).
The independently constructed actual C-component K₁ has quotient A₅ and
characteristic two; S=N_T(K₁) has index two and contains J(T). Finally the
original C_M(V)T normalizes L₀, retaining the group that contains the
opposite Borel in the source construction.

This assembles the proved source inputs without assuming the later F.1.1
amalgam or its exclusion. The strengthened theorem supplies Rc≤S through
the actual wreath-core bridge. Characteristic two of the actual parabolics,
the mixed DGS85 exclusion, and the subsequent
proper-local argument remain separate obligations of original15.2.4.
Source: Aschbacher--Smith15.2.4, printed pp.1106--1107.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- The actual wreath local yields the literal two quotient types and normalizer data. -/
theorem source_HStar_wreath_five_configuration
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
    let L₀ := Y ⊔ R
    let X := (pResidual 2 ↑(H ⊓ M)).map (H ⊓ M).subtype
    ∃ (l : LocalGeneration (ρ.comp (Jhat ρ).subtype)) (K₁ : Subgroup G),
      DihedralMarking l 5 2 ∧ K₁ ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* alternatingGroup (Fin 5)) ∧
      generalizedFitting K₁ = pCore 2 K₁ ∧ ¬ K₁ ≤ M ∧
      ((T : Subgroup G) ⊓ normalizer (K₁ : Set G)).relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) ⊓ normalizer (K₁ : Set G) ∧
      (∃ S₀ : Sylow 2 L₀, (S₀ : Subgroup L₀).map L₀.subtype = R) ∧
      (Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* DihedralGroup 5) ∨
        Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
      (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) ≤ normalizer (L₀ : Set G) ∧
      R ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨l,hd,_⟩ := source_HStar_wreath_five_reduction
    hG T hempty hM hJ hu hmany hV hcases hH he
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨K,hK,heK,hfit,hout,hi,hJS⟩ := source_HStar_symmetricFive_wreath_factor
    hG T hempty hM hJ hV hH he
  exact ⟨l,K,hd,hK,heK,hfit,hout,hi,hJS,
    source_dihedral_five_intersection_core_sylow hG T hempty hM hJ hu hmany hV l hp hd,
    source_dihedral_five_join_quotient hG T hempty hM hJ hu hmany hV l hp hd,
    (source_chosen_centralizer_sylow_normalizes_residual T hM.1.2 hu hV).2,
    source_chosen_intersection_core_le_HStar_core T hM.1.2 hu hV hH⟩

/-- The original intersection core belongs to the actual common Sylow subgroup. -/
theorem source_HStar_wreath_intersection_core_le_component_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V H K₁ : Subgroup G}
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K₁ ∈ Chapter1.cComponentsIn H) :
    (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (K₁ : Set G) :=
  (source_chosen_intersection_core_le_HStar_core T hM.1.2 hu hV hH).trans
    (source_HStar_symmetricFive_wreath_residual_core hG T hM hJ hH he hK)

/-- The literal configuration with the source common-Sylow containment discharged. -/
theorem source_HStar_wreath_five_configuration_with_Rc_le_S
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
    let L₀ := Y ⊔ R
    let X := (pResidual 2 ↑(H ⊓ M)).map (H ⊓ M).subtype
    ∃ (l : LocalGeneration (ρ.comp (Jhat ρ).subtype)) (K₁ : Subgroup G),
      DihedralMarking l 5 2 ∧ K₁ ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* alternatingGroup (Fin 5)) ∧
      generalizedFitting K₁ = pCore 2 K₁ ∧ ¬ K₁ ≤ M ∧
      ((T : Subgroup G) ⊓ normalizer (K₁ : Set G)).relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) ⊓ normalizer (K₁ : Set G) ∧
      (∃ S₀ : Sylow 2 L₀, (S₀ : Subgroup L₀).map L₀.subtype = R) ∧
      (Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* DihedralGroup 5) ∨
        Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
      (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) ≤ normalizer (L₀ : Set G) ∧
      R ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      R ≤ (T : Subgroup G) ⊓ normalizer (K₁ : Set G) := by
  obtain ⟨l,K,hd,hK,heK,hfit,hout,hi,hJS,hSyl,hquot,hNorm,hCore⟩ :=
    source_HStar_wreath_five_configuration hG T hempty hM hJ hu hmany hV hcases hH he
  exact ⟨l,K,hd,hK,heK,hfit,hout,hi,hJS,hSyl,hquot,hNorm,hCore,
    source_HStar_wreath_intersection_core_le_component_normalizer hG T hM hJ hu hV hH he hK⟩

end CFSG.Quasithin.Chapter15.Section02

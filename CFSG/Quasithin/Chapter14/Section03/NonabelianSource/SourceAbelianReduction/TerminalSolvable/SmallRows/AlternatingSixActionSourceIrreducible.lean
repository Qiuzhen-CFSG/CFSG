module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSource
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.FourSpace
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter.FlagModule
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource

/-!
# The irreducible terminal A₆ action and the remaining constituent inputs

If the specified A₆ component is irreducible on the whole terminal module,
the original elementary actor embeds in its automorphism group. Its two-rank
bound and G.10.2 give degree at most eight. The complete binary A₆ catalogue
leaves degrees one, four and sixteen; faithfulness excludes one. The actual
four-space recognition therefore supplies natural coordinates, and the literal
radical quotient adapter gives the required Sylow action.

For a reducible restriction, the final assembly below separates two source
obligations: a proper constituent through the marked point, and natural-module
coordinates from that constituent. Neither existence nor module recognition
is asserted by this conditional assembly; both inputs must still be proved
from the original flag geometry.

Source: Aschbacher--Smith G.5.1, G.10.2, G.11.6--9, and 14.3.15,
printed pp.342--343,357,365--369,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original source action is natural when its specified A₆ component
is irreducible on the whole hat module. No module marking is assumed. -/
theorem ComponentLift.alternatingSixNaturalAction_of_irreducible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    (hi : Representation.IsIrreducible (F.terminalRepresentation.comp (F.terminalDot K).subtype)) :
    hK.AlternatingSixNaturalAction e6 := by
  obtain ⟨hx,B,v,hyp,_⟩ := source_component_lift_geometry
    hG T hempty hM hu hmany hcard e F hne g hgP hgH K hK
  let := hx
  let L := F.terminalDot K
  let := hK.alternatingSix_image_normal hG e6
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) := hi
  let X := F.terminalDot (F.X g)
  let m := Module.finrank (ZMod 2) (Additive X)
  have hs : ChapterG.Section09.Setup F.terminalRepresentation X m := by
    refine ⟨hyp.faithful, inferInstance, ?_, ?_⟩
    · change Nat.card (Additive X) = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    · have hr := (Group.rank_le_of_surjective
        (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf X))
        (QuotientGroup.mk'_surjective _)).trans
          (IsElementaryAbelian.rank_le_finrank (p := 2) X)
      have hd := hyp.dimension_bound.1
      change Module.finrank (ZMod 2) (Additive F.Uhat) ≤
        2 * (Group.rank (X ⧸ (F.terminalDot (conjugate F.ZU g)).subgroupOf X) + 1) at hd
      exact hd.trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hr 1))
  have hr := hs.rank_le_automorphisms (L := L) le_normalizer_of_normal
  rw [primeRank_equiv 2 (MulAut.congr e6)] at hr
  have ha := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.alternating_six_automorphism_two_rank
  have hd8 : Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 8 := by
    have := hs.degree_le
    omega
  let σ := (F.terminalRepresentation.comp L.subtype).comp e6.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    e6.symm.toMonoidHom e6.symm.surjective _).mpr hi
  have hf : Function.Injective σ := (hyp.faithful.comp L.subtype_injective).comp e6.symm.injective
  have hlo := ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter.degree_ge_four σ hf
  have hdeg := BinaryAlternatingSix.alternating_degrees σ
  have hd4 : Module.finrank (ZMod 2) (Additive F.Uhat) = 4 := by omega
  obtain ⟨a⟩ := ChapterK.Alternating.RecognitionInputs.Six.actionEquiv_of_faithful_fourSpace σ hf hd4
  apply hK.alternatingSixNaturalAction_of_coordinates hG e6
  refine ⟨e6.trans a.groupEquiv, Or.inl ⟨a.linearEquiv, ?_⟩⟩
  intro k w
  have he := a.intertwines (e6 k) w
  simpa only [σ, L, ChapterB.QuasisimpleSource.alternatingNatural,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, MulEquiv.trans_apply] using he

/-- Assembly from the two independent proper-constituent source inputs.
The irreducible branch has already been discharged. The first input excludes
exchanged constituents; the second recognizes the actual homogeneous action. -/
theorem source_terminal_a6_natural_action_of_constituent_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (_hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hpoint : ¬ IsIrreducible (F.terminalRepresentation.comp (F.terminalDot K).subtype) →
      ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
        BinaryOffender.IsIrrPlus F.terminalRepresentation
          (componentOrbit (F.terminalDot K) ⊤) I ∧ v ∈ I ∧ I ≠ ⊤)
    (hcoordinates : ∀ I : Submodule (ZMod 2) (Additive F.Uhat),
      BinaryOffender.IsIrrPlus F.terminalRepresentation
        (componentOrbit (F.terminalDot K) ⊤) I → v ∈ I → I ≠ ⊤ →
      BinaryAlternatingSixNaturalNormalizer.HasNaturalCoordinates
        (F.terminalRepresentation.comp (F.terminalDot K).subtype)) :
    hK.AlternatingSixNaturalAction e6 := by
  by_cases hi : IsIrreducible (F.terminalRepresentation.comp (F.terminalDot K).subtype)
  · exact hK.alternatingSixNaturalAction_of_irreducible
      hG T hempty hM hu hmany hcard e F hne g hgP hgH e6 hi
  · obtain ⟨I,hI,hv,hproper⟩ := hpoint hi
    exact hK.alternatingSixNaturalAction_of_coordinates hG e6 (hcoordinates I hI hv hproper)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

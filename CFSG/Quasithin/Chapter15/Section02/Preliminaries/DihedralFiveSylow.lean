module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveSetup
public import Theory.GroupTheory.SylowNormalizedSupIndex
/-!
# The original intersection core is Sylow in the order-five residual join

The cyclic action kernel of the literal residual lies in O₂(M). Its image
has order five, so that kernel is a normal Sylow two-subgroup of Y and is
exactly O₂(Y). Thus [Y : O₂(Y)] = 5 and O₂(Y) ≤ O₂(M) ≤ Rc. The original
orbit construction makes Rc normalize Y. The odd-index supplement criterion
then proves Rc ∈ Syl₂(YRc), retaining the actual ambient subgroup maps.

This discharges the Sylow premise in the mixed-amalgam construction of
original15.2.4 without requiring the separate normality theorem Y ◁ M.
Source: Aschbacher--Smith15.2.4, printed p.1106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem kernel_five (T : Sylow 2 G) {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hc : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 5) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    (pCore 2 Y).index = 5 ∧ Y.pCoreIn 2 ≤ M.pCoreIn 2 := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let f : M →* internalActionImage M V hV.normalized := (actionHom M V hV.normalized).rangeRestrict
  have hYM : Y ≤ M := source_caseIIResidual_le T hTM (map_subtype_le _)
  let a := f.comp (inclusion hYM)
  have ha : a.range = (Y.subgroupOf M).map f := by
    ext d
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨⟨y,hYM y.property⟩,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  have hcyclic : IsCyclic ((Y.subgroupOf M).map f) := isCyclic_of_prime_card hc
  have hbound := source_chosen_cyclic_kernel_le_core T hTM hu hV hcyclic
  have hcore : a.ker.map Y.subtype ≤ M.pCoreIn 2 := by
    rintro x ⟨y,hy,rfl⟩
    change (y : G) ∈ (pCore 2 M).map M.subtype
    refine mem_map.mpr ⟨inclusion hYM y, hbound ⟨y.property, ?_⟩, rfl⟩
    exact congrArg Subtype.val hy
  have hi : a.ker.index = 5 := by
    rw [index_ker,ha]
    exact hc
  have hp : IsPGroup 2 a.ker := by
    have hh := (isPGroup_pCoreIn 2 M).to_le hcore
    exact hh.of_equiv (equivMapOfInjective a.ker Y.subtype Y.subtype_injective).symm
  let P : Sylow 2 Y := hp.toSylow (by rw [hi]; decide)
  have he : pCore 2 Y = a.ker := le_antisymm
    (pCore_isPGroup.le_sylow_of_normal P) (le_sSup ⟨inferInstance,hp⟩)
  refine ⟨he ▸ hi,?_⟩
  change (pCore 2 Y).map Y.subtype ≤ M.pCoreIn 2
  rwa [he]

private theorem residual_notation (K : Subgroup G) :
    twoResidualAmbient K = (pResidual 2 K).map K.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN,n,hn⟩
    exact ⟨hN,IsPGroup.of_card hn⟩
  · rintro ⟨hN,hn⟩
    exact ⟨hN,IsPGroup.iff_card.mp hn⟩

section ChosenFive
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype)) {m : ℕ}
    (hp : PrimeDimensionOptions 5 m) (hd : DihedralMarking l 5 m)
include hG hempty hM hJ hu hmany hp hd

/-- The original five residual has two-core of index five, contained in the selected core. -/
theorem source_dihedral_five_residual_core_index :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    (pCore 2 Y).index = 5 ∧ Y.pCoreIn 2 ≤ M.pCoreIn 2 := by
  apply kernel_five T hM.1.2 hu hV
  have he := source_dihedral_caseIIResidual_image hG T hempty hM hJ hu hmany hV l hp hd
  exact (congrArg (fun K : Subgroup (internalActionImage M V hV.normalized) => Nat.card K) he).trans
    ((card_map_of_injective (Jhat (imageRepresentation M V hV.normalized)).subtype_injective).trans
      hd.card_kernel)

/-- The literal Rc is the ambient image of a Sylow two-subgroup of YRc. -/
theorem source_dihedral_five_intersection_core_sylow :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let R := (M ⊓ Mc).pCoreIn 2
    ∃ S : Sylow 2 ↑(Y ⊔ R), (S : Subgroup ↑(Y ⊔ R)).map (Y ⊔ R).subtype = R := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let R := (M ⊓ Mc).pCoreIn 2
  let A := twoResidualAmbient (chosenStarredPreimage M V hV.normalized) ⊔ (T : Subgroup G)
  let K := conjugateSpanBy R A
  have hYR : Y = (pResidual 2 K).map K.subtype := residual_notation K
  have hRn : R ≤ normalizer (Y : Set G) := by
    rw [hYR]
    exact (le_conjugateSpanBy R A).trans (K.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K (pResidual 2 K)))
  obtain ⟨hi,hcore⟩ := source_dihedral_five_residual_core_index hG T hempty hM hJ hu hmany hV l hp hd
  apply IsPGroup.exists_sylow_sup_of_coprime_index Y R (isPGroup_pCoreIn 2 (M ⊓ Mc)) hRn (pCore 2 Y)
  · rw [hi]
    decide
  · exact hcore.trans ((hV.intersection_core_centralizer T hM.1.2 hu).symm.le.trans inf_le_left)
end ChosenFive
end CFSG.Quasithin.Chapter15.Section02

module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentData
public import Theory.GroupTheory.RelativeSylowNormalizer

/-!
# Sylow and Thompson control in the Case-I centralizer

For every marked subgroup Z₁ of the actual chosen fixed space, the subgroup
S=C_T(Z₁) has the same elementary Thompson and Baumann subgroups as T.
The source Baumann control therefore places N_G(S) in M. This promotes the
literal local Sylow subgroup of C_M(Z₁) to a Sylow subgroup of C_G(Z₁),
without changing its embedding. The initial local Sylow fact is the marked
row calculation of 15.1.16; the component-data consumer retains it explicitly.

Source: Aschbacher--Smith 15.1.17 and 15.1.18(4), printed p.1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterB Chapter14.SourcePreliminaries Chapter12.Section08
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The common Thompson and normalizer part of original 15.1.17. -/
theorem PreparedChosenModule.caseI_marked_thompson_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) ∧
      baumann S = baumann (T : Subgroup G) ∧
      (baumann S).characteristicNormalizerClosure ≤ M ∧
      normalizer (S : Set G) ≤ M := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  have hZV : Z1 ≤ localModule T M := (hZ.trans inf_le_left).trans h.le_local
  obtain ⟨hJZ, _, hB, hc⟩ := source_submodule_baumann_control hG T hM hJ Z1 hZV
  have hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ S :=
    le_inf (sSup_le fun _ hA => hA.1) hJZ
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq S (T : Subgroup G) inf_le_left
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le (T : Subgroup G) S hJS
  have horder : elementaryAbelianMaxOrder S = elementaryAbelianMaxOrder (T : Subgroup G) :=
    le_antisymm hsmall.1 hlarge.1
  have hJeq : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) :=
    le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)
  have hnorm : normalizer (S : Set G) ≤ M := by
    have hn := normalizer_le_normalizer_elementaryAbelianMaxJ S
    rw [hJeq] at hn
    exact hn.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  exact ⟨hJeq,hB.symm,by rwa [←hB],hnorm⟩

/-- Promote the marked local Sylow subgroup as in original 15.1.18(4). -/
theorem PreparedChosenModule.caseI_centralizer_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hSyl : ∃ P : Sylow 2 (centralizer (Z1 : Set G) ⊓ M : Subgroup G),
      (P : Subgroup (centralizer (Z1 : Set G) ⊓ M : Subgroup G)).map
        (centralizer (Z1 : Set G) ⊓ M).subtype =
        (T : Subgroup G) ⊓ centralizer (Z1 : Set G)) :
    ∃ P : Sylow 2 (centralizer (Z1 : Set G)),
      (P : Subgroup (centralizer (Z1 : Set G))).map
        (centralizer (Z1 : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer (Z1 : Set G) := by
  have hn := (h.caseI_marked_thompson_control hG T hM hJ hZ).2.2.2
  exact exists_sylow_eq_of_relative_normalizer_le hSyl inf_le_left
    (le_inf inf_le_left (inf_le_right.trans hn))

namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Apply the common control to the literal source component data. -/
theorem sylow_and_thompson_control (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hSyl : ∃ P : Sylow 2 (d.G1 ⊓ M : Subgroup G),
      (P : Subgroup (d.G1 ⊓ M : Subgroup G)).map (d.G1 ⊓ M).subtype = d.S) :
    (∃ P : Sylow 2 d.G1, (P : Subgroup d.G1).map d.G1.subtype = d.S) ∧
      elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) ∧
      baumann d.S = baumann (T : Subgroup G) ∧
      (baumann d.S).characteristicNormalizerClosure ≤ M ∧
      normalizer (d.S : Set G) ≤ M :=
  ⟨h.caseI_centralizer_sylow hG T hM hJ d.Z1_le_fixed hSyl,
    h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed⟩
end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01

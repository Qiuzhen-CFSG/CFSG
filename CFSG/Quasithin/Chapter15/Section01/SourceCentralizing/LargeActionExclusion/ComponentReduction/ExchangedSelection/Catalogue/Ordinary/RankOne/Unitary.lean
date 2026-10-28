module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Unitary.Normality
public import Theory.SpecificGroups.SU3.OrdinaryBorelTransport

/-!
# The ordinary unitary exclusion from original Thompson control

Odd-prime rank forces the unitary component to be normal in G₁. The
concrete fixed-field torus geometry supplies a two-perfect subgroup of the
literal Borel which normalizes J(S) and has the same Sylow centralizer as L.
Original J(S)=J(T) and its normalizer control put that subgroup in M; the
source residual-intersection identity then contradicts the noncentral
moving subgroup. No model or Thompson callback remains.
Source: Aschbacher--Smith 15.1.21(iii), printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
open HermitianForm HermitianForm.BorelTorus HermitianForm.OrdinaryBorel
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The actual unitary row supplies a two-perfect subgroup of the literal
Borel, normalizing J(S), with its exact centralizer comparison. -/
theorem PreExclusionSource.rankOne_unitary_geometry
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSU d.L 3 (2^n)) :
    ∃ B : Subgroup G, B ≤ d.ordinaryBorel ∧ IsPPerfect 2 B ∧
      B ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) ∧
      d.S ⊓ centralizer (B : Set G) ≤ d.S ⊓ centralizer (d.L : Set G) := by
  have hnormal := s.rankOne_unitary_normal (h := h) hG hL hn hm
  have hSL : d.S ≤ normalizer (d.L : Set G) := d.S_le_G1.trans
    ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp hnormal)
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  obtain ⟨P,hP⟩ := s.component_sylow
  have hSP : d.S.subgroupOf d.L = (P : Subgroup d.L) := by
    apply map_injective d.L.subtype_injective
    rw [hP,subgroupOf_map_subtype]
    rfl
  have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  obtain ⟨B,hBB,hperfect,hthompson,hfix⟩ :=
    exists_thompson_borel_subgroup J hn hF hconj d.L d.S hSL e P hSP
  refine ⟨B,?_,hperfect,hthompson,hfix⟩
  change B ≤ (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype
  change B ≤ (normalizer ((P : Subgroup d.L) : Set d.L)).map d.L.subtype at hBB
  rwa [hP'] at hBB

/-- The literal ordinary unitary Borel row is impossible, using original Thompson control. -/
theorem PreExclusionSource.false_of_rankOne_unitary
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSU d.L 3 (2^n))
    (hB : d.ML=d.ordinaryBorel) : False := by
  obtain ⟨B,hBB,hperfect,hthompson,hfix⟩ := s.rankOne_unitary_geometry (h := h) hG hL hn hm
  exact s.no_thompson_borel (h := h) hG hM hJ hperfect
    (hBB.trans (hB ▸ d.ML_le_MZ)) hthompson hfix
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

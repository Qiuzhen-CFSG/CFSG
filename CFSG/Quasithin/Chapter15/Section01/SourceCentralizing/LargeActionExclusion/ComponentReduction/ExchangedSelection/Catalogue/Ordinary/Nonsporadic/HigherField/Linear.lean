module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.FixedSolvable
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Solvable
public import Theory.SpecificGroups.PSL3.SylowFixedSolvable

/-!
# The complete initial higher-field linear exclusion

For PSL₃(2ⁿ), n > 1, and every retained central two-cover of PSL₃(4),
nonidentity Sylow fixers have solvable fixed groups. Original 14.1.6
therefore forces the actual M_L to be solvable. Its Borel equality follows
from solvable Sylow control and 15.1.19(2); the checked 15.1.21 contradiction
then applies. This discharges the Borel premise under the original markings.

Both the group and two-core quotient identifications are kept literally.
The original-marker consumer excludes the whole linear family at that same
d, before any exchanged selection. The literal earlier 15.1.14 residual
remains for its existing producer and qt-e-15122-pre-exclusion-catalogue;
remaining model families and Ordinary22 stay with the ordinary owner.
Source: Aschbacher--Smith, printed pp.977,1094--1098.
-/

public section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The fixed-group calculation lifts through the actual perfect central cover. -/
theorem PreExclusionSource.linear_quotient_local_solvable
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (d.L ⧸ pCore 2 d.L) ≃* PSL(3,F)) : Group.IsSolvable d.ML := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let ec := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  apply s.local_solvable_of_sylow_fixed_solvable (h := h) hG hempty hM hu hL
  intro P a ha hfix
  apply MulAut.fixed_solvable_of_centralQuotient ec _ P a ha hfix
  intro Q b hb hQ
  apply Matrix.PSL3.LinearThree.sylow_fixed_solvable F hn hF Q b _ hQ
  intro he
  rw [he,orderOf_one] at hb
  omega
/-- An actual PSL₃ marking supplies local solvability for every binary field. -/
theorem PreExclusionSource.linear_local_solvable
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : d.L ≃* PSL(3,F)) : Group.IsSolvable d.ML := by
  apply s.local_solvable_of_sylow_fixed_solvable (h := h) hG hempty hM hu hL
  intro P a ha hfix
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let b := MulAut.congr e a
  have hb : b ≠ 1 := by
    intro he
    have he' : a = 1 := (MulAut.congr e).injective (he.trans (map_one _).symm)
    rw [he',orderOf_one] at ha
    omega
  have hQ : ∀ x ∈ Q, b x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hfix x hx]
  let : Group.IsSolvable b.fixedSubgroup :=
    Matrix.PSL3.LinearThree.sylow_fixed_solvable F hn hF Q b hb hQ
  exact Group.isSolvable_of_isSolvable_injective
    (f := (MulAut.fixedSubgroupCongr e a).toMonoidHom)
    (MulAut.fixedSubgroupCongr e a).injective

/-- The initial higher-field linear branch is impossible, including every retained
central two-cover of PSL₃(4). Its Borel premise is proved, not assumed. -/
theorem PreExclusionSource.false_of_initial_linear_higherField
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : (∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSL d.L 3 (2^n)) ∨
      ClassicalGroup.IsPSL (d.L ⧸ pCore 2 d.L) 3 4) : False := by
  have hh : d.OrdinaryHigherField := by
    rcases hm with ⟨n,hn,hm⟩ | hm
    · exact .inl ⟨n,hn,.inl hm⟩
    · exact .inr hm
  apply s.false_of_higherField_solvable (h := h) hG hM hJ hu hne hmany hres hL hh
  rcases hm with ⟨n,hn,F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · exact s.linear_local_solvable (h := h) hG hempty hM hu hL (by omega) hF e
  · exact s.linear_quotient_local_solvable (h := h) hG hempty hM hu hL
      (n := 2) (by decide) (by simpa using hF) e
/-- After the initial linear exclusions, a higher-field model must be symplectic. -/
theorem PreExclusionSource.higherField_symplectic
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : d.OrdinaryHigherField) :
    ∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSp d.L 2 (2^n) := by
  rcases hm with ⟨n,hn,hm | hm⟩ | hm
  · exact (s.false_of_initial_linear_higherField (h := h) hG hempty hM hJ hu hne
      hmany hres hL (.inl ⟨n,hn,hm⟩)).elim
  · exact ⟨n,hn,hm⟩
  · exact (s.false_of_initial_linear_higherField (h := h) hG hempty hM hJ hu hne
      hmany hres hL (.inr hm)).elim

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- At the original marker, higher-field linear groups and their retained central
covers are excluded. The literal earlier residual remains for final assembly. -/
theorem PreparedChosenModule.source_preExclusion_higherField_symplectic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.OrdinaryHigherField →
        ∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSp d.L 2 (2^n)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL hm => s.higherField_symplectic (h := h)
    hG hempty hM hJ hu hne hmany hres hL hm⟩
end CFSG.Quasithin.Chapter15.Section01

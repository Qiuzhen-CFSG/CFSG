module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Setup
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.ResidualGeneration
public import Theory.GroupTheory.CComponent.LocalOrbitSolvable
public import Theory.GroupTheory.CComponent.ConstrainedPrimeJoin
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# Solvable characteristic-two closure of each source parabolic

The literal S₃ or S₃-wreath quotient makes P a {2,3}-group. Solvability
passes from P to its orbit under S inside the marked C-component.
For characteristic two, ordinary components use the local core-orbit theorem;
constrained components use characteristic two of LS and Sylow inheritance.
Neither argument assumes that S normalizes L or that G₁ has characteristic two.

Source: Aschbacher--Smith 15.1.22(*), printed pp.1098--1099.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
open Section03 Section03.InitialSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem IsSourceParabolic.solvable
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P) :
    Group.IsSolvable P := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro q hq hd
  exact (IsPiGroup_iff _ _).mp hP.twoThree ⟨q,hq⟩ hd

theorem IsSourceParabolic.closure_solvable
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P) :
    Group.IsSolvable (d.parabolicClosure P) := by
  exact d.L_component.2.relative_local_adjoin_isSolvable d.L_component.1 hP.le_component
    d.S_le_G1 (T.isPGroup'.to_le d.S_le_T) hP.normalized hP.solvable

theorem PreExclusionSource.parabolicClosure_fitting
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    {P : Subgroup G} (hP : d.IsSourceParabolic P) :
    generalizedFitting (d.parabolicClosure P) = pCore 2 (d.parabolicClosure P) := by
  rcases d.L_component.2.component_or_generalizedFitting_eq_pCore s.odd_core with hc | hf
  · apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    apply (inf_centralizer_pCoreIn_le_iff 2 (d.parabolicClosure P)).mp
    exact hc.relative_local_adjoin_centralizer d.L_component.1 hP.le_component
      d.S_le_G1 (T.isPGroup'.to_le d.S_le_T) hP.normalized
      ((inf_centralizer_pCoreIn_le_iff 2 P).mpr
        ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hP.fitting))
  · let A := d.L.subgroupOf d.G1
    let B := d.S.subgroupOf d.G1
    let X := P.subgroupOf d.G1 ⊔ B
    let K := A ⊔ B
    have hfit : centralizer (pCore 2 K : Set K) ≤ pCore 2 K :=
      d.L_component.2.constrained_join_characteristicTwo
        (T.isPGroup'.to_le d.S_le_T).comap_subtype s.odd_core hf
    obtain ⟨R,hR⟩ := s.centralizer_sylow
    have hRB : (R : Subgroup d.G1) = B := by
      apply map_injective d.G1.subtype_injective
      rw [hR, map_subgroupOf_eq_of_le d.S_le_G1]
    have hXF := generalizedFitting_eq_pCore_of_sylow_overgroup R X K
      (hRB ▸ le_sup_right)
      (sup_le_sup (subgroupOf_mono d.G1 hP.le_component) le_rfl) hfit
    have hm : X.map d.G1.subtype = d.parabolicClosure P := by
      change (P.subgroupOf d.G1 ⊔ d.S.subgroupOf d.G1).map d.G1.subtype = P ⊔ d.S
      rw [Subgroup.map_sup]
      exact congrArg₂ (· ⊔ ·)
        (map_subgroupOf_eq_of_le (show P ≤ d.G1 from hP.le_component.trans d.L_component.1))
        (map_subgroupOf_eq_of_le d.S_le_G1)
    let e : X ≃* d.parabolicClosure P :=
      (X.equivMapOfInjective d.G1.subtype d.G1.subtype_injective).trans (MulEquiv.subgroupCongr hm)
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
        ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hXF))
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.LocalReduction.FixedPart
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.Contracts
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfSylow

/-!
# The natural local reduction before the terminal TI construction

The natural full automizer bound excludes zero corank. A positive central
kernel gives a nonidentity offender action kernel, forcing both moved factors
into the opposite local group and contradicting E.3.25. The fixed part is
therefore zero, and the outside-local intersection theorem gives global TI.

The only earlier input retained is the component-normalizer conclusion of
10.2.6. The adapter consumes its existing half-Sylow uniqueness contract;
that source theorem remains with its point-control owner. The small-offender
owner retains the terminal TI construction and final assembly.
Source: Aschbacher--Smith 10.2.10(2) and 10.2.12, printed pp.753--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}

/-- The literal moved factor is TI when its fixed kernel vanishes. -/
theorem natural_moved_ti_of_moved_fixed_eq_bot
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hz : ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥) :
    IsTISubgroup ⁅D.fullModule,L⁆ := by
  obtain ⟨t,ht,htn,_,_,hperm⟩ := source_nonnormal_fullModule_pair D c.nonnormal
  have hdis : ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom = ⊥ :=
    bot_unique ((inf_le_inf_left _ (m.crossed t ht htn)).trans_eq hz)
  have hti := map_conj_eq_or_inf_eq_bot_of_conj_pair D.maximalLocal ⁅D.fullModule,L⁆
    ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) hperm hdis
    (fun _ hx => natural_outside_intersection c m hNL hx)
  intro x hx v hv
  have he := (hti x).resolve_left (fun he => hx (mem_normalizer_iff_map_conj_eq.mpr he))
  have hv' : v ∈ ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom := hv
  exact he.le hv'

/-- The entire local corank-one reduction, without a survivor or later w=2
premise. All action, cardinality, fixed-part and TI steps are proved. -/
theorem natural_local_reduction
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1) :
    subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) = 1 ∧
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
    IsTISubgroup ⁅D.fullModule,L⁆ := by
  have hz := moved_fixed_eq_bot_of_small_corank c m hNL hsmall
  exact ⟨(natural_corank_one_and_reverse_escape c m hNL hsmall).1,
    full_fixed_eq_bot_of_moved_fixed_eq_bot m c.nonnormal hz,
    natural_moved_ti_of_moved_fixed_eq_bot c m hNL hz⟩

/-- The existing earlier half-Sylow contract discharges the sole remaining
normalizer premise of the published local reduction contract. -/
theorem localReduction_of_halfSylowUnique
    (hhalf : PointControl.HalfSylowUniqueAt T) : LocalReductionAt T := by
  intro L D g c m hsmall
  exact natural_local_reduction c m
    (PointControl.component_normalizer_le_of_halfSylowUnique D c.nonnormal
      (hhalf c.many L D c.nonnormal c.notA5)) hsmall

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank

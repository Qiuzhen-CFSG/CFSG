module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.SourceAction.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Applicability
public import Theory.SpecificGroups.BinaryLinear.FourResidual

/-!
# Source action inputs following 13.6.23

The source configuration retains full Hypothesis 13.3.1, its uniform A₅
choice, the actual marked A₅ module, and the original z and v. It also
retains all three literal conclusions of 13.6.23: the O^{3′} residual,
the actual SL₄(2) model with a noninner diagram actor, and the middle-node
minimal parabolic in that same model. No module classification is a field.

The local Sylow, central-seed and characteristic-two conclusions give the
literal W_K its elementary structure and kill the plus two-core. The
checked SL₄(2)–A₈ comparison then gives the compatible full S₈ action.
The component is faithful on U_K, and the original K-class descends to it.
Both W_K and U_K are proved FF for the full plus actor. The remaining
ordinary FF assertion for K⁺ on U_K requires a component-offender transfer;
none of the theorems here identifies that assertion with full-actor FF.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Hypothesis 13.3.1, printed p.884; 13.6.2–16, pp.926–930;
13.6.23 and its following paragraph, printed p.933/PDF p.950.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.SourceAction
open ComponentSelection SourceContainment.LinearThree.CentralAction
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Conditional source data for the paragraph following 13.6.23. The
outer selection owner constructs these earlier-source premises. In
particular the residual is O^{3′}, and the marked parabolic and diagram
action use the actual plus quotient of the original W_K. -/
structure Configuration (𝒦 : GroupClass.{u}) (K L V : Subgroup G)
    (T : Sylow 2 G) (z v : G) where
  standing : ModuleAlternatives.Applicability.SourceHypothesis 𝒦 T L
  marking : A5Module.Marking L V
  marked_z : z = A5Module.markedZ marking
  marked_v : v = A5Module.markedV marking
  a5 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  counterexample : IsA5Counterexample G
  lv_invariant : Tv (T : Subgroup G) v ≤ normalizer (Lv L v : Set G)
  seed_fixed : Tv (T : Subgroup G) v ≤ centralizer ({z} : Set G)
  sylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v)
  seed_omega : z ∈ omegaOneCenterAmbient (Tv (T : Subgroup G) v)
  v_order : orderOf v = 2
  characteristic_two : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)
  selected : K ∈ Yz L (T : Subgroup G) z v
  invariant : Tv (T : Subgroup G) v ≤ normalizer (K : Set G)
  lv_le : Lv L v ≤ K
  seed_moved : ¬ Lv L v ≤ centralizer ({z} : Set G)
  /-- The three genuine earlier conclusions of 13.6.16, for every allowed replacement. -/
  earlier_control : ∀ K₀ : Subgroup G,
    K₀ ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v) →
    Tv (T : Subgroup G) v ≤ normalizer (K₀ : Set G) →
    ¬ K₀ ≤ centralizer ({z} : Set G) →
    (K₀ ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥ ∧
      (∀ C : Subgroup (Tv (T : Subgroup G) v), C.Characteristic → C ≠ ⊥ →
        (solvableRadical K₀).map K₀.subtype ⊔
          (K₀ ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G)) < K₀) ∧
      ⁅K₀, elementaryAbelianMaxJ (Tv (T : Subgroup G) v)⁆ = K₀
  residual : K = (primeToResidual 3 (Gv v)).map (Gv v).subtype
  linear_four : plusImage K L (T : Subgroup G) z v lv_invariant seed_fixed K ≃* SL(4, ZMod 2)
  diagram :
    let C := plusImage K L (T : Subgroup G) z v lv_invariant seed_fixed K
    letI : C.Normal := plusComponent_normal K L (T : Subgroup G) z v
      lv_invariant seed_fixed lv_le invariant
    ∃ t ∈ plusImage K L (T : Subgroup G) z v lv_invariant seed_fixed (Tv (T : Subgroup G) v),
      componentAction C (linear_four.trans (slEquivLinear 4)) t ∉ MulAut.innerSubgroup _
  basis : Basis 3
  middle_parabolic :
    ((plusImage K L (T : Subgroup G) z v lv_invariant seed_fixed
      (sourceParabolic K L (T : Subgroup G) v)).subgroupOf
        (plusImage K L (T : Subgroup G) z v lv_invariant seed_fixed K)).map
      (linear_four.trans (slEquivLinear 4)).toMonoidHom = minimalParabolic basis 1

variable {𝒦 : GroupClass.{u}} {K L V : Subgroup G} {T : Sylow 2 G} {z v : G}
    (c : Configuration 𝒦 K L V T z v)

/-- The A₈ marking is obtained from the actual SL₄(2) marking by the
checked exceptional isomorphism, not chosen independently. -/
noncomputable def Configuration.alternating :
    plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed K ≃*
      alternatingGroup (Fin 8) :=
  c.linear_four.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)

include c in
/-- The source elementary module is constructed; it is not a configuration field. -/
theorem Configuration.elementary : IsElementaryAbelian 2 (WK K L (T : Subgroup G) z v) :=
  wk_elementary K L (T : Subgroup G) z v c.selected c.sylow c.seed_omega c.characteristic_two

/-- The R₂ conclusion uses the literal kernel of conjugation on W_K. -/
theorem Configuration.twoCore :
    pCore 2 (Gplus K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed) = ⊥ :=
  plus_twoCore_eq_bot K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed c.selected c.sylow

/-- Noninner action in the original linear marking is an actual element
outside K⁺. The R₂ argument discharges the self-centralizer condition. -/
theorem Configuration.outside :
    ¬ plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed (Tv (T : Subgroup G) v) ≤
      plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed K := by
  let C := plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed K
  let : C.Normal := plusComponent_normal K L (T : Subgroup G) z v
    c.lv_invariant c.seed_fixed c.lv_le c.invariant
  have ht : IsPGroup 2 (Tv (T : Subgroup G) v) :=
    T.isPGroup'.to_le inf_le_left
  have hc := plusComponent_centralizer_eq_bot K L (T : Subgroup G) z v
    c.lv_invariant c.seed_fixed c.invariant c.lv_le c.alternating ht c.twoCore
  obtain ⟨t, ht, houter⟩ := c.diagram
  intro hle
  exact houter ((componentAction_mem_inner C (c.linear_four.trans (slEquivLinear 4)) hc t).mpr
    (hle ht))

/-- The model-independent classifier preparation applies to the original
A₈ configuration. Its cover and kernel are constructed from K₋L_vT_v;
no L₃(2) identification or offender-generation premise is used. -/
theorem Configuration.applicability :
    letI := c.elementary
    ModuleAlternatives.ClassifierApplicability 𝒦
      (representation K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed)
      (plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed K) :=
  ModuleAlternatives.classifierApplicability_of_local c.standing.qtke
    K L (T : Subgroup G) z v c.v_order c.lv_invariant c.seed_fixed c.sylow c.seed_omega
    c.characteristic_two c.selected c.invariant

/-- All constructed preparation data on the actual source action. The last
FF assertion retains Gplus as its actor. Component FF is deliberately not
asserted here and remains the input needed for the B.5.1 application. -/
theorem source_action_inputs :
    let := c.elementary
    let ρ := representation K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
    let C := plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed K
    let s := movedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed c.invariant c.lv_le
    pCore 2 (Gplus K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed) = ⊥ ∧
      Function.Injective ρ ∧ IsSQTK 𝒦 C ∧
      Function.Injective (s.space.toRepresentation.comp C.subtype) ∧
      C ≤ offenderSubgroup ρ ∧ IsFFModule ρ ∧ IsFFModule s.space.toRepresentation ∧
      ∃ E : Gplus K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed ≃* Equiv.Perm (Fin 8),
        (∀ k : C, E k = (c.alternating k).val) ∧
        C.map E.toMonoidHom = alternatingGroup (Fin 8) := by
  let := c.elementary
  have hzT := ((mem_omegaOneCenterAmbient_iff (Tv (T : Subgroup G) v) z).mp c.seed_omega).1
  have ht : IsPGroup 2 (Tv (T : Subgroup G) v) :=
    T.isPGroup'.to_le inf_le_left
  have hsource : IsKGroup 𝒦 (Gv v) :=
    (c.standing.qtke.involution_centralizer_sqtk c.v_order).2
  refine ⟨c.twoCore, representation_injective K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed,
    component_sqtk K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed c.selected hsource c.alternating,
    component_moved_faithful K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
      c.selected c.twoCore c.alternating _,
    component_le_offenders K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
      c.selected c.invariant hzT c.sylow,
    wk_isFF K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed c.selected c.invariant hzT c.sylow,
    moved_isFF_full_actor K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
      c.selected c.invariant c.lv_le hzT c.sylow, ?_⟩
  exact exists_marked_symmetricEquiv K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
    c.invariant c.lv_le c.alternating ht c.twoCore c.outside

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.SourceAction

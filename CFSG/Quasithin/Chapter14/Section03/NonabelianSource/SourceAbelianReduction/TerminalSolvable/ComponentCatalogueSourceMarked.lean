module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedComplete
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceAssembly

/-!
# Retaining the actual tensor marking in the terminal catalogue

For an original marked constituent, a nonfaithful actor has either two
copies or higher multiplicity. The sharp degree theorem in the first case,
and the actual alternating orbit in the second, make the original component
normal. A proper faithful constituent likewise has a single component.
Consequently every nonnormal marked component acts on the whole space and
has the genuine binary determinant tensor model already constructed by the
marked-image recognition. Lift the same component, preserving its literal
T-conjugate span, before applying the quotient sieve.

The resulting terminal consumer has only the normalized A₅ Borel exclusion,
the full exchanged wreath quotient, and the L₂(8) exclusion as premises on
the marked branch. The unmarked constituent branch is treated separately;
no paired direct sum is identified with the tensor representation.
Source: Aschbacher–Smith G.11.6–9 and 14.3.15, printed pp.365–369 and 994.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative MatrixGroups
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- Nonfaithful marked actors have a single original component. Normality
is recovered before the component image is sent through the catalogue. -/
theorem component_normal_of_not_actorFaithful
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I)) : L.Normal := by
  rcases s.constituent_dimension_cases_of_not_actorFaithful hk with hd | hd
  · exact s.orbit_eq_component_of_double_dimension hk hd ▸ componentOrbit_top_normal L
  · obtain ⟨n,hn,_,a,_,_⟩ := s.source_higher_natural_model hk hd
    exact (s.component_eq_orbit_of_alternating n hn a).symm ▸ componentOrbit_top_normal L

/-- A nonnormal marked component has the whole terminal module as its
chosen constituent. This is the premise required by tensor recognition. -/
theorem whole_of_component_not_normal (hn : ¬ L.Normal) : I = ⊤ := by
  by_cases hf : ActorFaithful (F := F) (g := g) (I := I)
  · by_contra hi
    exact hn (s.orbit_eq_component_of_actorFaithful_of_ne_top hf hi ▸
      componentOrbit_top_normal L)
  · exact (hn (s.component_normal_of_not_actorFaithful hf)).elim

/-- The actual local lift has either its normalized T-span or the genuine
tensor action. The same K occurs in the image, quotient and action markings. -/
theorem local_lift_normalized_or_tensor :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K ∧
      (K = conjugateSpanBy K (T : Subgroup G) ∨
        Nonempty (ExchangedA5.ActionModel F K)) := by
  obtain ⟨K,hKH,hlocal,hcomp,he,_,hnormal⟩ :=
    Recognition.terminal_component_lift s.simple F (by decide) L s.component
  change F.terminalDot K = L at he
  have hK : ComponentLift F g K :=
    ⟨hKH,hlocal,hcomp,he.symm ▸ s.component,he.symm ▸ s.moved,hnormal⟩
  refine ⟨K,hK,source_component_cases_of_small_actor s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card s.centralizer_quotient.some
    F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.hypothesis s.small_actor
    hK (he.symm ▸ s.recognized_componentImageCases),?_⟩
  by_cases hn : L.Normal
  · exact Or.inl (hK.eq_conjugateSpanBy_of_image_normal (he.symm ▸ hn))
  · have hi := s.whole_of_component_not_normal hn
    have hHL : componentOrbit L ⊤ ≠ L :=
      fun hh => hn (hh ▸ componentOrbit_top_normal L)
    exact Or.inr (s.actionModel_of_whole_pair_eight hi hHL
      (s.degree_eight_of_whole_pair hi hHL) hK he)

/-- After the original quotient and A₆ sieves, every marked source yields
normalized A₅, L₂(8), or the actual exchanged tensor action. -/
theorem normalized_a5_or_eight_or_tensor :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      ((K = conjugateSpanBy K (T : Subgroup G) ∧
        Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5))) ∨
       EightImageRow F K ∨ Nonempty (ExchangedA5.ActionModel F K)) := by
  obtain ⟨K,hK,hcases,hspan | htensor⟩ := s.local_lift_normalized_or_tensor
  · rcases source_component_cases_reduce s.simple T s.empty s.maximal s.unique_overgroup
        s.many_overgroups s.seed_card s.centralizer_quotient.some s.not_model
        F g K hK hcases with h5 | h8
    · rcases h5 with h5 | h6
      · exact ⟨K,hK,Or.inl ⟨hspan,h5⟩⟩
      · exact (source_terminal_a6_false s.simple T s.empty s.maximal s.unique_overgroup
          s.many_overgroups s.seed_card s.centralizer_quotient.some s.not_model
          F s.nonabelian g s.parabolic_mem s.normalizer_not_mem hK h6.some).elim
    · exact ⟨K,hK,Or.inr (Or.inl h8)⟩
  · exact ⟨K,hK,Or.inr (Or.inr htensor)⟩

end MarkedSource
namespace ExchangedFaithfulSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)
include s

/-- The recognized A₇ orbit is the same original component; its ambient
normality supplies the source quotient sieve, closing this branch entirely. -/
theorem false_of_source : False := by
  let H := componentOrbit L ⊤
  let eH : H ≃* alternatingGroup (Fin 7) :=
    (ExchangedAction.orbitEquiv F.terminalRepresentation H (F.terminalDot (F.X g))
      I s.selected.invariant s.orbit_faithful).trans s.image_alternating_seven.some
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup H := eH.isSimpleGroup
  have hLH : L ≤ H := le_componentOrbit L ⊤
  have heq : L = H := by
    rcases s.component.1.subgroupOf.eq_bot_or_top_of_isSimpleGroup
        (inferInstance : IsSimpleGroup H) with hb | ht
    · have he := congrArg (Subgroup.map H.subtype) hb
      rw [map_subgroupOf_eq_of_le hLH,Subgroup.map_bot] at he
      exact (s.moved (by rw [he,commutator_bot_left])).elim
    · exact le_antisymm hLH (subgroupOf_eq_top.mp ht)
  have hn : L.Normal := heq.symm ▸ componentOrbit_top_normal L
  let eL := (MulEquiv.subgroupCongr heq).trans eH
  obtain ⟨K,hKH,hlocal,hcomp,he,_,hnormal⟩ :=
    Recognition.terminal_component_lift s.simple F (by decide) L s.component
  change F.terminalDot K = L at he
  have hK : ComponentLift F g K :=
    ⟨hKH,hlocal,hcomp,he.symm ▸ s.component,he.symm ▸ s.moved,hnormal⟩
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card s.centralizer_quotient.some
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  have hk := (Recognition.rankTwo_small_actor_geometry h F g d s.nonabelian
    s.parabolic_mem s.normalizer_not_mem s.hypothesis s.small_actor).2.2.2.2
  exact source_excluded_quotient_row_false s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card s.centralizer_quotient.some s.not_model F g K hK
    (hK.eq_conjugateSpanBy_of_image_normal (he.symm ▸ hn))
    (Or.inr (Or.inl ⟨(hK.twoCoreQuotientEquivDot hk).trans
      ((MulEquiv.subgroupCongr he).trans eL)⟩))
end ExchangedFaithfulSource

namespace ExchangedCentralSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)
include s

/-- Original exchanged constituents with central action kernel cannot occur,
by the recognized A₇ orbit and the original ambient quotient sieve. -/
theorem false_of_source : False := s.faithful_source.false_of_source
end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

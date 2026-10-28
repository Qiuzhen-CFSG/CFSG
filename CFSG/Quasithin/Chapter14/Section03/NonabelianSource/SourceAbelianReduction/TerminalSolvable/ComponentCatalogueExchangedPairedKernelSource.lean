module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedRank
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedContracts
public import Theory.Frattini.PGroup
public import CFSG.Quasithin.ChapterG.Section10.Components.ExchangedFaithfulPair

/-!
# The literal noncentral-kernel exchanged source

All original ambient and constituent-selection clauses are retained. The
noncentral kernel is the kernel of the same H-action on the chosen I.
The two exchanged actions jointly separate H before any full-module spanning
or properness premise is used. The noncentral kernel also forces the original
component to be nonnormal, hence to have an orbit of size exactly two.

This supplies the initial source geometry for paired A5; elementary Sylow
factors and their final recognition remain separate proof obligations.
Source: Aschbacher--Smith G.10.15, printed pp.362--363; 14.3.12--15,
printed pp.993--994.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative

/-- The original noncentral-kernel branch, with the same chosen constituent. -/
structure ExchangedPairedSource {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M Mc : Subgroup G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (L : Subgroup F.TerminalHdot) (I : Submodule (ZMod 2) (Additive F.Uhat)) : Prop where
  simple : IsSimpleQTKE KnownSimple.IsKnownSimple G
  empty : MainForward.faithfulLocalComponents T = ∅
  maximal : IsOrderingMaximal T M
  unique_overgroup : maximalTwoLocalOvergroups
    (centralizer (centralInvolutions T : Set G)) = {Mc}
  many_overgroups : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  seed_card : Nat.card (localModule T M) = 4
  centralizer_quotient : Nonempty
    ((M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
  not_model : ¬ ClassificationModels.IsTheoremEModel G
  nonabelian : ¬ IsMulCommutative F.U
  parabolic_mem : g ∈ F.P (sourceResidual M Mc)
  normalizer_not_mem : g ∉ F.H
  nonsolvable : ¬ Group.IsSolvable F.TerminalHdot
  hypothesis : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))
  small_actor : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
    Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1
  component : IsComponent F.TerminalHdot L
  moved : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥
  orthogonal : ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L
  fixedSpace_eq_bot : fixedSpace F.terminalRepresentation (componentOrbit L ⊤) = ⊥
  commutator_eq_top : subspaceCommutator F.terminalRepresentation ⊤ (componentOrbit L ⊤) = ⊤
  selected : Homogeneous.IsIrrPlusWith F.terminalRepresentation
    (componentOrbit L ⊤) (F.terminalDot (F.X g)) I
  irreducible : IsIrreducible
    (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I selected.invariant).toRepresentation
  conjugate_span :
    let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
    (⨆ a : F.TerminalHdot, conjugateSubrepresentation F.terminalRepresentation
      (componentOrbit L ⊤)
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I selected.invariant) a) = ⊤
  conjugate_disjoint : ∀ a : F.TerminalHdot,
    I.map (F.terminalRepresentation a) = I ∨ Disjoint (I.map (F.terminalRepresentation a)) I
  form_cases : (∀ u ∈ I, ∀ w ∈ I, B u w = 0) ∨ (B.restrict I).Nondegenerate
  dimension_gt_two : 2 < Module.finrank (ZMod 2) I
  independent : sSupIndep (subspaceOrbit F.terminalRepresentation (F.terminalDot (F.X g)) I)
  point_not_mem : v ∉ I
  noncentral_kernel :
    ¬ (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      selected.invariant).toRepresentation.asGroupHom.ker ≤
        Subgroup.center (componentOrbit L ⊤)

namespace ExchangedPairedSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedPairedSource T M Mc F g B v L I)

/-- The Sylow subgroup obtained from the original T, with its literal quotient map. -/
abbrev pointSylow : Sylow 2 F.TerminalHdot :=
  (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)

include s

/-- Normality of the normal component orbit transfers the original G.10.3
conclusion to its intrinsic two-core. -/
theorem orbit_twoCore_eq_bot : pCore 2 (componentOrbit L ⊤) = ⊥ := by
  let hn := componentOrbit_top_normal L
  rw [pCore_subnormal_eq_comap 2 hn.isSubnormal, s.hypothesis.twoCore_eq_bot]
  apply bot_unique
  intro x hx
  exact mem_bot.mpr (Subtype.ext (show (x : F.TerminalHdot) = 1 from hx))

/-- The original actor is contained in, and normalized by, the actual source Sylow. -/
theorem actor_sylow :
    F.terminalDot (F.X g) ≤ (pointSylow (F := F) : Subgroup F.TerminalHdot) ∧
    (pointSylow (F := F) : Subgroup F.TerminalHdot) ≤
      normalizer (F.terminalDot (F.X g) : Set F.TerminalHdot) := by
  obtain ⟨_,hXP,hN⟩ := Recognition.source_terminal_actor_normal_in_point_sylow
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.hypothesis
  exact ⟨hXP,(normal_subgroupOf_iff_le_normalizer hXP).mp hN⟩

/-- G.10.9(2) on the literal original actor and the original Sylow intersection.
Its Frattini subgroup is intrinsic to the commutator subgroup. -/
theorem sylow_commutator :
    let C := ⁅F.terminalDot (F.X g),
      (pointSylow (F := F) : Subgroup F.TerminalHdot) ⊓ componentOrbit L ⊤⁆
    C ≤ F.terminalDot (F.X g) ⊓ componentOrbit L ⊤ ∧
    IsElementaryAbelian 2 C ∧ frattini C = ⊥ := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let C := ⁅F.terminalDot (F.X g),
    (pointSylow (F := F) : Subgroup F.TerminalHdot) ⊓ H⁆
  have hCX : C ≤ F.terminalDot (F.X g) :=
    le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans s.actor_sylow.2)
  have hCH : C ≤ H :=
    (commutator_mono le_rfl inf_le_right).trans (commutator_le_right _ _)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion hCX) (inclusion_injective hCX)
  let : Fact (IsPGroup 2 C) := ⟨IsElementaryAbelian.isPGroup 2 C⟩
  exact ⟨le_inf hCX hCH,inferInstance,frattini_eq_bot_of_isElementaryAbelian (p := 2)⟩


/-- The actual exchanged pair separates H, without a non-GL or spanning premise. -/
theorem pair_separates :
    ∃ x : F.terminalDot (F.X g), I.map (F.terminalRepresentation x) ≠ I ∧
      let H := componentOrbit L ⊤
      letI : H.Normal := componentOrbit_top_normal L
      let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
      let C := conjugateSubrepresentationOrderIso F.terminalRepresentation H (x:F.TerminalHdot) R
      ∀ a : H, R.toRepresentation a = 1 → C.toRepresentation a = 1 → a = 1 :=
  s.hypothesis.exchanged_pair_separates s.nonsolvable s.component s.moved
    (pointSylow (F:=F)) s.actor_sylow.2
    (Recognition.terminal_component_normalizer_index_le_two s.simple F (by decide) L s.component)
    s.selected s.point_not_mem

/-- A noncentral constituent kernel is impossible for a single quasisimple orbit. -/
theorem not_normal : ¬ L.Normal := by
  intro hLn
  let : L.Normal := hLn
  let H := componentOrbit L ⊤
  have hH : H = L := by
    apply le_antisymm _ (le_componentOrbit L ⊤)
    exact iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl
      (by rw [normalizer_eq_top])
  let : IsQuasisimple H := hH.symm ▸ s.component.2
  let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
  rcases IsQuasisimple.normal_le_center_or_eq_top R.toRepresentation.asGroupHom.ker with hc|ht
  · exact s.noncentral_kernel hc
  · have hfix : I ≤ fixedSpace F.terminalRepresentation H := by
      intro u hu a
      have he : R.toRepresentation.asGroupHom a = 1 :=
        MonoidHom.mem_ker.mp (ht ▸ mem_top a)
      exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) I =>
        (f.val ⟨u,hu⟩ : Additive F.Uhat)) he
    exact s.selected.isIrrPlus.ne_bot F.terminalRepresentation
      (bot_unique (s.fixedSpace_eq_bot ▸ hfix))

/-- The original component normalizer has index exactly two. -/
theorem normalizer_index_eq_two : (normalizer (L : Set F.TerminalHdot)).index = 2 := by
  have hi := Recognition.terminal_component_normalizer_index_le_two
    s.simple F (by decide) L s.component
  have hz := (normalizer (L : Set F.TerminalHdot)).index_ne_zero_of_finite
  have h1 : (normalizer (L : Set F.TerminalHdot)).index ≠ 1 :=
    fun he => s.not_normal (normalizer_eq_top_iff.mp (index_eq_one.mp he))
  omega


end ExchangedPairedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

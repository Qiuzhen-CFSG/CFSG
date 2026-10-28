module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Semisimple.Action
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Irreducible.BinaryThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.FourNaturalCrossed
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.NaturalDual
public import Theory.Representation.PSL3Two.SmallSemisimple
public import Theory.Representation.PSL3Two.DoubledCommuting
public import Theory.Representation.BinaryConjugationSection.Coinvariants

/-!
# Quiet binary-three recognition through dimension eight

Clifford theory supplies semisimplicity of the actual moved central quotient.
Its commutator generation removes fixed vectors. The small semisimple
catalogue then gives an irreducible, doubled-natural, or natural-plus-dual
action. Existing offender bounds exclude the adjoint and mixed rows. A
Singer obstruction supplies crossed centralization in the doubled row;
minimality and the original cubic residual then exclude that row as well.

The result constructs natural coordinates whenever the literal quotient
has order below 512, including nonirreducible candidates. The larger quiet
quotients and the other unmarked families remain source obligations of
qt-d-10-nona5-small-offender. The component normalizer premise retains the
existing half-Sylow producer and final point-control discharge.
Source: Aschbacher–Smith D.3.21,10.1.1 and10.2.12, pp.204–207,741,754–755.
-/

public noncomputable section
open scoped MonoidAlgebra IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private def doubleCoordinates : (BinaryLinearThree.W.prod BinaryLinearThree.W).Equiv
    (SL3DoubledNaturalOffenders.representation (ZMod 2)) where
  toLinearEquiv := (LinearEquiv.piFinTwo (ZMod 2) (fun _ => BinaryLinearThree.Vector)).symm
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext i j
    fin_cases i <;> rfl

private def reversePair : (BinaryLinearThree.W.dual.prod BinaryLinearThree.W).Equiv
    (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) where
  toLinearEquiv := LinearEquiv.prodComm _ _ _
  isIntertwining' _ := rfl

private def doubleDualCoordinates : (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual).Equiv
    ((SL3DoubledNaturalOffenders.representation (ZMod 2)).comp
      BinaryLinearThree.AutomorphismAction.graph.toMonoidHom) where
  toLinearEquiv := (BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm.toLinearEquiv.prodCongr
    BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm.toLinearEquiv).trans
    doubleCoordinates.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    ext i j
    fin_cases i
    · exact congrFun (LinearMap.congr_fun (BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm.isIntertwining' g) v.1) j
    · exact congrFun (LinearMap.congr_fun (BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm.isIntertwining' g) v.2) j

set_option backward.isDefEq.respectTransparency false in
theorem doubled_crossed_of_minimal
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule) (hrow : ModuleChoice.BinaryThreeDoubled D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  by_cases hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)
  swap
  · exact ModuleChoice.crossed_of_local_thompson D hJ ht htn
  by_cases hz : D.fullModule ⊓ centralizer (L : Set G) = ⊥
  swap
  · exact ModuleChoice.quiet_crossed_of_component_fixed_ne_bot D hmany hmin hJ ht htn hz
  rcases quiet_crossed_or_moved_eq_full D hmany hmin hJ ht htn with hcross | hw
  · exact hcross
  obtain ⟨e,⟨d⟩⟩ := hrow
  let : IsElementaryAbelian 2 D.fullModule :=
    D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hs : ChapterB.QuasisimpleSource.repeated
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3) 2 =
      SL3DoubledNaturalOffenders.representation (ZMod 2) := by
    ext g v i j
    rfl
  rw [hs] at d
  let d0 : BinaryConjugationSection L D.fullModule ⊥
      ((SL3DoubledNaturalOffenders.representation (ZMod 2)).comp q) := by
    simpa only [sourceMovedFixed,hw,hz,q] using d
  obtain ⟨τ,hτ⟩ := d0.exists_commuting_conjugate
    (SL3DoubledNaturalOffenders.representation (ZMod 2)) q hq
    (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))
    (opposite_commutator_centralizes_fullModule D ht htn)
  exact (BinaryLinearThree.DoubledNatural.not_commuting_conjugate τ hτ).elim

theorem no_doubled_of_minimal
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ¬ ModuleChoice.BinaryThreeDoubled D := by
  intro hrow
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  exact ModuleChoice.not_binaryThreeDoubled_of_minimal D hmin ht htn
    (doubled_crossed_of_minimal D hmany hmin hrow ht htn) hrow

theorem natural_of_quiet_binary_three_small_section
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group V) (hf : Function.Injective σ)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hdim : Module.finrank (ZMod 2) V < 9) : BinaryThreeNatural D := by
  let : IsSemisimpleModule (ZMod 2)[BinaryLinearThree.Group] σ.asModule :=
    quiet_moved_section_semisimple D c.many c.minimal c.nonnormal hJ σ e s
  have hgen : Coinvariants.ker σ = ⊤ :=
    s.coinvariants_eq_top_of_group_generation L le_rfl σ
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) (fun _ _ => rfl) (by
      rw [commutator_comm,source_full_moved_eq_commutator D,sup_eq_left.mpr inf_le_left])
  have hfix := invariants_eq_bot_of_semisimple_of_coinvariants_eq_top σ hgen
  let : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : Nontrivial V := by
    by_contra hn
    let : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    obtain ⟨a,ha⟩ := exists_ne (1 : BinaryLinearThree.Group)
    exact ha (hf (Subsingleton.elim _ _))
  rcases BinaryLinearThree.small_semisimple_alternatives σ hfix hdim with hi | hd | hm | hm | hd
  · exact natural_of_irreducible_binary_three_section D c hNL σ hf hi e s
  · obtain ⟨a⟩ := hd
    apply False.elim
    apply no_doubled_of_minimal D c.many c.minimal c.nonnormal
    exact ⟨e,⟨s.relabel _ (a.trans doubleCoordinates)⟩⟩
  · obtain ⟨a⟩ := hm
    exact (no_natural_dual_of_small_offender D c ⟨e,⟨s.relabel _ a⟩⟩ hNL).elim
  · obtain ⟨a⟩ := hm
    exact (no_natural_dual_of_small_offender D c ⟨e,⟨s.relabel _ (a.trans reversePair)⟩⟩ hNL).elim
  · obtain ⟨a⟩ := hd
    apply False.elim
    apply no_doubled_of_minimal D c.many c.minimal c.nonnormal
    exact ⟨e.trans BinaryLinearThree.AutomorphismAction.graph,
      ⟨s.relabel _ (a.trans doubleDualCoordinates)⟩⟩

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition

namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The intrinsic quotient-size form has no irreducibility or model-marking assumption. -/
theorem natural_of_quiet_binary_three_small_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (hsize : (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ < 512) :
    BinaryThreeNatural D := by
  let := source_full_moved_elementary D
  let σ := binaryThreeMovedAction D c.nonnormal e
  let s := binaryThreeMovedSection D c.nonnormal e
  apply natural_of_quiet_binary_three_small_section D c hJ hNL σ
    (binaryThreeMovedAction_faithful D c.nonnormal e) e s
  let Q := Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅D.fullModule,L⁆)
  have hc : (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ = Nat.card Q := by
    have h := Nat.card_congr s.quotientEquiv.toEquiv
    change (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ = Nat.card Q at h
    simpa only [inf_relIndex_left] using h
  have hp : 2 ^ Module.finrank (ZMod 2) Q < 2 ^ 9 := by
    rw [hc,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hsize
    exact hsize
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hp

/-- Any unrecognized quiet binary-three offender has moved central quotient
of order at least 512. The natural conclusion is the literal source marking. -/
theorem quiet_binary_three_natural_or_large_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    BinaryThreeNatural D ∨
      512 ≤ (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ := by
  by_cases hs : (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ < 512
  · exact Or.inl (natural_of_quiet_binary_three_small_quotient D c hJ hNL e hs)
  · exact Or.inr (by omega)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition

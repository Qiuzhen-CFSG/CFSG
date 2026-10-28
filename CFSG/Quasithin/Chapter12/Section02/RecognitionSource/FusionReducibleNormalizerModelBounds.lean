module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerChosenControl
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerChosenCover
public import Theory.Representation.G2BinaryFixedBounds
public import Theory.Representation.PSL3Two.NaturalDualCohomology
public import Theory.Representation.PSL3Two.NaturalSylowFixed

/-!
# Transporting central-cover bounds to the original chosen module

A marked full action with a surjective projection whose kernel is exactly
its fixed space induces coordinates on the literal quotient V/C_V(L).
This retains L/O₂(L) and the original conjugation action. The natural-module
cohomology and Sylow bounds then give |C_V(L)|=2 and |C_V(T)|≤4, so the
chosen-module normalizer theorem applies without an intrinsic block premise.

Source: Aschbacher–Smith B.4.8(2), I.2.3 and 12.2.16, pp.91,413,799–800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A central-cover marking descends to the actual chosen central quotient. -/
def chosenCentralEquiv_of_cover (D : ChosenModule T L V)
    {A W U : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U]
    {σ : Representation (ZMod 2) A W} {τ : Representation (ZMod 2) A U}
    (e : ActionEquiv D.quotientAction σ) (p : σ.IntertwiningMap τ)
    (hp : Function.Surjective p) (hk : p.toLinearMap.ker = OneCohomology.fixed σ) :
    ActionEquiv D.centralQuotientAction τ := by
  let C := G2WeylModel.Fixed D
  let f := p.toLinearMap.comp e.linearEquiv.toLinearMap
  have hc (v : D.space) : v ∈ C ↔ ∀ q, D.quotientAction q v = v := by
    constructor
    · intro hv q
      obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
      exact Subtype.ext (hv ((subgroupOfEquivOfLe
        (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l))
    · intro hv l
      exact congrArg Subtype.val (hv (QuotientGroup.mk' (pCore 2 L) ⟨l.val.val,l.property⟩))
  have hker : f.ker = C := by
    ext v
    change e.linearEquiv v ∈ p.toLinearMap.ker ↔ v ∈ C
    rw [hk,hc]
    constructor
    · intro hv q
      apply e.linearEquiv.injective
      rw [e.intertwines,hv]
    · intro hv a
      obtain ⟨q,rfl⟩ := e.groupEquiv.surjective a
      rw [← e.intertwines,hv]
  let fq : D.chosenCentralQuotient →ₗ[ZMod 2] U := C.liftQ f hker.ge
  have hbij : Function.Bijective fq := ⟨by
      apply LinearMap.ker_eq_bot.mp
      rw [Submodule.ker_liftQ,hker]
      exact Submodule.mkQ_map_self C,
    by
      intro w
      obtain ⟨v,rfl⟩ := hp.comp e.linearEquiv.surjective w
      exact ⟨Submodule.Quotient.mk v,rfl⟩⟩
  refine ⟨e.groupEquiv,LinearEquiv.ofBijective fq hbij,?_⟩
  intro q v
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change p (e.linearEquiv (D.quotientAction (QuotientGroup.mk' (pCore 2 L) l) v)) = _
    exact (congrArg p (e.intertwines _ v)).trans (p.isIntertwining _ _ _ _)

/-- The precise natural quotient and its two bounds suffice for normalizer control. -/
theorem sylow_normalizer_le_of_chosen_central_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) A W}
    (e : ActionEquiv D.centralQuotientAction σ)
    (hH : Module.finrank (ZMod 2) (H1 σ.dual) ≤ 1)
    (hS : ∀ P : Sylow 2 A, Nat.card (fixedSpace σ (P : Subgroup A)) ≤ 2) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  have hc := ChosenCover.fixed_card_eq_two D e hne hH
  exact sylow_normalizer_le_of_chosen_fixed_bounds h D structural hnone hc
    (ChosenCover.sylow_fixed_card_le_four D e hc hS)

/-- The natural G₂ central-quotient row supplies its own normalizer premise. -/
theorem sylow_normalizer_le_of_g2_central_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : ActionEquiv D.centralQuotientAction (g2DerivedNatural (ZMod 2))) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_chosen_central_model h D structural hnone hne e
    Atlas.G2.Natural.BinarySylowFixedSpace.derived_natural_dual_H1_finrank.le
    Atlas.G2.Natural.BinarySylowFixedSpace.card_derived_sylow_fixed_le_two

/-- The full seven-dimensional Weyl action supplies the literal natural quotient. -/
theorem sylow_normalizer_le_of_g2_weyl_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : ActionEquiv D.quotientAction (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2))) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let p := Atlas.G2.Natural.OrthogonalCover.projection (ZMod 2)
  have hp := Atlas.G2.Natural.OrthogonalCover.projection_isCover (ZMod 2)
  apply sylow_normalizer_le_of_g2_central_model h D structural hnone hne
  exact chosenCentralEquiv_of_cover D e p hp.1
    (by rw [Atlas.G2.Natural.OrthogonalCover.projection_ker,
      Atlas.G2.Natural.OrthogonalCover.fixed_eq_scalarLine])

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

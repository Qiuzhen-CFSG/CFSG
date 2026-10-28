module

public import Theory.Representation.G2NaturalRootCentralizers
public import Theory.Representation.G2OrthogonalCover.ParabolicFixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.FixedSpaces

/-!
# The scalar term in the original G₂ root-centralizer span

The actual chosen central cover is a quotient of the Weyl module, over its
supplied natural projection. Fixed vectors lift through that projection,
so the Weyl root-centralizer span maps onto the literal fixed-space span
on D.space. The concrete root calculation then gives

  [E,A₁] + C_V(L) = V₃,

and equality without the central summand holds exactly when C_V(L)=1.
Here V₃ is the original preimage of the standard natural three-space;
markedThreePreimage_mem gives its ambient membership formula.

This identifies an obstruction to constructing RootSpan.moved from the
local B.4.6 model facts alone. RootPlaneData uses the full flag preimage,
so an ambient argument removing or recovering the central term is still
needed. We do not assert that the entire NonbinaryNaturalInput has a
counterexample. No changes are made to the existing conditional assembly.

Source: Aschbacher–Smith, B.4.6(3,7), printed p.88, and 11.2.2(5), printed
p.768. The universal-cover map is the existing original-action theorem.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
open Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- The upper natural three-space pulled back along the original chosen
central quotient and the supplied G₂ marking. -/
def markedThreePreimage : Submodule (ZMod 2) D.space :=
  ((Atlas.G2.NaturalOffenders.upper (F := S.field.Carrier)).restrictScalars (ZMod 2)).comap
    (((Atlas.G2.Restricted.NaturalCoordinates.coordinates S.field.Carrier).restrictScalars
      (ZMod 2)).comp (Preliminary.markedProjection D m).toLinearMap)


/-- The actual fixed-space span on the chosen module, over the same model
long-root groups used by B.4.6(3). -/
def markedRootSpan : Submodule (ZMod 2) D.space :=
  ⨆ Z ∈ RootCentralizers.longRoots S.field.Carrier,
    fixedSpace (Preliminary.markedAction D m) Z

private theorem original_fixedSpan_map
    (p : (RootCentralizers.coverAction S.field.Carrier).IntertwiningMap
      (Preliminary.markedAction D m))
    (hp : Function.Surjective p)
    (hover : ∀ x, Preliminary.markedProjection D m (p x) = mk S.field.Carrier x) :
    (RootCentralizers.fixedSpan S.field.Carrier).map p.toLinearMap = markedRootSpan D S m := by
  unfold RootCentralizers.fixedSpan markedRootSpan
  rw [Submodule.map_iSup]
  apply iSup_congr
  intro Z
  rw [Submodule.map_iSup]
  apply iSup_congr
  intro _
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩ a
    have he := LinearMap.congr_fun (p.isIntertwining' a.val) x
    change p (RootCentralizers.coverAction S.field.Carrier a.val x) =
      Preliminary.markedAction D m a.val (p x) at he
    have hx' : RootCentralizers.coverAction S.field.Carrier a.val x = x := hx a
    rw [hx'] at he
    exact he.symm
  · intro v hv
    obtain ⟨x,rfl⟩ := hp v
    refine ⟨x,?_,rfl⟩
    intro a
    apply Extensions.traceZero_fixed_of_natural_fixed
    have he := LinearMap.congr_fun ((Preliminary.markedProjection D m).isIntertwining' a.val) (p x)
    change Preliminary.markedProjection D m
      (Preliminary.markedAction D m a.val (p x)) =
      action S.field.Carrier a.val (Preliminary.markedProjection D m (p x)) at he
    have hv' : Preliminary.markedAction D m a.val (p x) = p x := hv a
    rw [hv',hover] at he
    exact he.symm

/-- Membership is in the literal ambient preimage under the supplied marking. -/
theorem markedThreePreimage_mem (v : D.space) : v ∈ markedThreePreimage D S m ↔
    (D.spaceEquiv (Multiplicative.ofAdd v) : G) ∈
      (Coordinates.g2 m).preimage ((Atlas.G2.NaturalOffenders.upper (F := S.field.Carrier)).comap
        (Atlas.G2.Restricted.NaturalCoordinates.coordinates S.field.Carrier)) := by
  rw [(Coordinates.g2 m).mem_preimage]
  change Atlas.G2.Restricted.NaturalCoordinates.coordinates S.field.Carrier
    (m.linearEquiv ((Preliminary.centralSpace D).mkQ v)) ∈ Atlas.G2.NaturalOffenders.upper ↔
    Atlas.G2.Restricted.NaturalCoordinates.coordinates S.field.Carrier
      (m.linearEquiv ((Preliminary.centralSpace D).mkQ
        (D.spaceEquiv.symm (D.spaceEquiv (Multiplicative.ofAdd v))).toAdd)) ∈
        Atlas.G2.NaturalOffenders.upper
  rw [D.spaceEquiv.symm_apply_apply]
  rfl

private theorem original_preimage_map
    (p : (RootCentralizers.coverAction S.field.Carrier).IntertwiningMap
      (Preliminary.markedAction D m))
    (hp : Function.Surjective p)
    (hover : ∀ x, Preliminary.markedProjection D m (p x) = mk S.field.Carrier x) :
    (RootCentralizers.threePreimage S.field.Carrier).map p.toLinearMap =
      markedThreePreimage D S m := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change Atlas.G2.Restricted.NaturalCoordinates.coordinates S.field.Carrier
      (Preliminary.markedProjection D m (p x)) ∈ Atlas.G2.NaturalOffenders.upper
    rw [hover]
    exact hx
  · intro v hv
    obtain ⟨x,rfl⟩ := hp v
    refine ⟨x,?_,rfl⟩
    change Atlas.G2.Restricted.NaturalCoordinates.coordinates S.field.Carrier
      (Preliminary.markedProjection D m (p x)) ∈ Atlas.G2.NaturalOffenders.upper at hv
    rw [hover] at hv
    exact hv

private theorem original_scalar_map
    (p : (RootCentralizers.coverAction S.field.Carrier).IntertwiningMap
      (Preliminary.markedAction D m))
    (hp : Function.Surjective p)
    (hover : ∀ x, Preliminary.markedProjection D m (p x) = mk S.field.Carrier x) :
    ((scalarLine S.field.Carrier).restrictScalars (ZMod 2)).map p.toLinearMap =
      Preliminary.centralSpace D := by
  rw [← Preliminary.markedProjection_ker D m]
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change Preliminary.markedProjection D m (p x) = 0
    rw [hover]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  · intro v hv
    obtain ⟨x,rfl⟩ := hp v
    refine ⟨x,?_,rfl⟩
    change Preliminary.markedProjection D m (p x) = 0 at hv
    rw [hover] at hv
    exact (Submodule.Quotient.mk_eq_zero _).mp hv


omit [Finite G] in
private theorem centralSpace_eq_bot_iff : Preliminary.centralSpace D = ⊥ ↔
    V ⊓ centralizer (L : Set G) = ⊥ := by
  rw [← Submodule.subsingleton_iff_eq_bot, (Preliminary.centralSpaceEquiv D).subsingleton_congr]
  constructor
  · intro h
    let := h
    exact Subgroup.eq_bot_of_subsingleton _
  · intro h
    rw [h]
    infer_instance

/-- The actual chosen-module application: the root commutator equals the
full third preimage exactly when the original central space is zero. The
cover map is constructed, and intertwines the entire marked G₂ action. -/
private theorem exists_original_root_cover :
    ∃ p : (RootCentralizers.coverAction S.field.Carrier).IntertwiningMap
        (Preliminary.markedAction D m),
      Function.Surjective p ∧
      (∀ x, Preliminary.markedProjection D m (p x) = mk S.field.Carrier x) ∧
      subspaceCommutator (Preliminary.markedAction D m)
          ((RootCentralizers.fixedSpan S.field.Carrier).map p.toLinearMap)
          (Atlas.G2.EvenTwoRank.elementary S.field.Carrier) ⊔ Preliminary.centralSpace D =
        markedThreePreimage D S m ∧
      (subspaceCommutator (Preliminary.markedAction D m)
          ((RootCentralizers.fixedSpan S.field.Carrier).map p.toLinearMap)
          (Atlas.G2.EvenTwoRank.elementary S.field.Carrier) = markedThreePreimage D S m ↔
        V ⊓ centralizer (L : Set G) = ⊥) := by
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary)
  obtain ⟨p,hp,hover⟩ := OrthogonalCover.ParabolicFixed.exists_full_quotient S.field.Carrier
    (Preliminary.markedProjection D m) hq (Preliminary.markedProjection_isCover D m)
  have hker : p.toLinearMap.ker ≤ (scalarLine S.field.Carrier).restrictScalars (ZMod 2) := by
    intro x hx
    change p x = 0 at hx
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change mk S.field.Carrier x = 0
    rw [← hover,hx,map_zero]
  have hpre := original_preimage_map D S m p hp hover
  have hscalar := original_scalar_map D S m p hp hover
  refine ⟨p,hp,hover,?_,?_⟩
  · have he := congrArg (Submodule.map p.toLinearMap)
      (RootCentralizers.root_commutator_sup_scalar S.field.Carrier)
    rw [Submodule.map_sup,RootCentralizers.map_root_commutator,hscalar,hpre] at he
    exact he
  · have he := RootCentralizers.root_commutator_image_eq_iff S.field.Carrier p.toLinearMap hker
    rw [RootCentralizers.map_root_commutator,hscalar,hpre] at he
    exact he.trans (centralSpace_eq_bot_iff D)


/-- The central term is necessary in the literal chosen-module root-span
identity. In particular, dropping it requires C_V(L)=1. -/
theorem original_root_span_commutator :
    subspaceCommutator (Preliminary.markedAction D m) (markedRootSpan D S m)
        (Atlas.G2.EvenTwoRank.elementary S.field.Carrier) ⊔ Preliminary.centralSpace D =
      markedThreePreimage D S m ∧
    (subspaceCommutator (Preliminary.markedAction D m) (markedRootSpan D S m)
        (Atlas.G2.EvenTwoRank.elementary S.field.Carrier) = markedThreePreimage D S m ↔
      V ⊓ centralizer (L : Set G) = ⊥) := by
  obtain ⟨p,hp,hover,hsum,heq⟩ := exists_original_root_cover D S m
  rw [original_fixedSpan_map D S m p hp hover] at hsum heq
  exact ⟨hsum,heq⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2

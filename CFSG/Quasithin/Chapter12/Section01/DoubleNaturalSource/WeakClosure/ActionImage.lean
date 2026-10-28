module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ModelGeometry

/-!
# The literal doubled-orbit action image

The normalizer equality identifies the range of the branch's actual conjugation
with Aut_G(W). The first isomorphism theorem transports the literal quotient
marking to that range, and the component-action equation remains unchanged.
The two coordinate kernels retain the original natural and dual summands.
A noncentralizing conjugate has zero intersection with the natural summand
under the explicit pure-intersection hypothesis.

These are action and intersection bridges for 12.1.8 and 12.1.10, not a
construction of the full equivariant H.9 model or either weak-closure bound.
Source: Aschbacher--Smith, combined manuscript, pp.389,792--794.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)

/-- The original normalizer action has precisely the full ambient automizer
as image once the normalizer identity is known. -/
theorem normalizerAction_range
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G)) :
    (normalizerAction T L V B.orbit_eq).range = Automizer (componentOrbit V (T : Subgroup G)) := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    exact ⟨inclusion (by rw [B.orbit_eq]; exact le_normalizer_componentOrbit _ _) m, rfl⟩
  · rintro _ ⟨m, rfl⟩
    refine ⟨⟨m, hNM ▸ m.property⟩, ?_⟩
    rfl

/-- First isomorphism theorem for the literal quotient in the doubled branch. -/
def quotientEquivAutomizer
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G)) :
    (normalizer (L : Set G) ⧸ (normalizerAction T L V B.orbit_eq).ker) ≃*
      Automizer (componentOrbit V (T : Subgroup G)) :=
  (QuotientGroup.quotientKerEquivRange (normalizerAction T L V B.orbit_eq)).trans
    (MulEquiv.subgroupCongr (B.normalizerAction_range hNM))

/-- This isomorphism carries a quotient representative to its actual conjugation. -/
theorem quotientEquivAutomizer_mk
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (m : normalizer (L : Set G)) (w : componentOrbit V (T : Subgroup G)) :
    (((B.quotientEquivAutomizer hNM (QuotientGroup.mk' _ m) :
      Automizer (componentOrbit V (T : Subgroup G))) :
      MulAut (componentOrbit V (T : Subgroup G))) w : G) =
      (m : G) * (w : G) * (m : G)⁻¹ := rfl

/-- The abstract group identification is transported from the literal quotient.
Equivariance for a model action is a separate obligation. -/
def automizerEquivAut
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G)) :
    Automizer (componentOrbit V (T : Subgroup G)) ≃* MulAut (BinaryLinear.OuterCyclic.LinearGroup n) :=
  (B.quotientEquivAutomizer hNM).symm.trans B.full

/-- The actual image of an element of L in the action on the full orbit. -/
def componentActor : L →* Automizer (componentOrbit V (T : Subgroup G)) :=
  (componentOrbit V (T : Subgroup G)).normalizerMonoidHom.rangeRestrict.comp
    (inclusion (by rw [B.orbit_eq]; exact L.le_normalizer.trans (le_normalizer_componentOrbit _ _)))

/-- The given component marking intertwines the actual component automizer
with the natural-plus-dual action. -/
theorem componentActor_coordinates (l : L) (w : componentOrbit V (T : Subgroup G)) :
    B.coordinates ((B.componentActor l).val w) = Multiplicative.ofAdd
      (BinaryNaturalDual.naturalDualRepresentation (B.component (QuotientGroup.mk' (pCore 2 L) l))
        (B.coordinates w).toAdd) := by
  apply B.coordinates.symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  exact (B.component_action l w).symm

/-- The same component-action identity on the actual binary vector space. -/
theorem componentActor_linearCoordinates
    [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
    (l : L) (w : Additive (componentOrbit V (T : Subgroup G))) :
    B.linearCoordinates (automizerRepresentation (componentOrbit V (T : Subgroup G))
      (B.componentActor l) w) =
    BinaryNaturalDual.naturalDualRepresentation (B.component (QuotientGroup.mk' (pCore 2 L) l))
      (B.linearCoordinates w) :=
  congrArg Multiplicative.toAdd (B.componentActor_coordinates l w.toMul)

variable [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- The original natural summand, pulled back through the branch coordinates. -/
def naturalSpace : Submodule (ZMod 2) (Additive (componentOrbit V (T : Subgroup G))) :=
  (LinearMap.snd (ZMod 2) (BinaryLinear.OuterCyclic.Space n)
    (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))).ker.comap
      B.linearCoordinates.toLinearMap

/-- The original dual summand, with the same coordinates as the natural one. -/
def dualSpace : Submodule (ZMod 2) (Additive (componentOrbit V (T : Subgroup G))) :=
  (LinearMap.fst (ZMod 2) (BinaryLinear.OuterCyclic.Space n)
    (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))).ker.comap
      B.linearCoordinates.toLinearMap

@[simp] theorem mem_naturalSpace (w : Additive (componentOrbit V (T : Subgroup G))) :
    w ∈ B.naturalSpace ↔ (B.coordinates w.toMul).toAdd.2 = 0 := Iff.rfl

@[simp] theorem mem_dualSpace (w : Additive (componentOrbit V (T : Subgroup G))) :
    w ∈ B.dualSpace ↔ (B.coordinates w.toMul).toAdd.1 = 0 := Iff.rfl

/-- The source pure-intersection input forces the natural intersection with
an actual noncentralizing conjugate to vanish. -/
theorem natural_intersection_eq_bot (hp : B.PureIntersectionCentralizes) (g : G)
    (hg : ⁅componentOrbit V (T : Subgroup G),
      (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    B.naturalSpace ⊓ subgroupSpace (componentOrbit V (T : Subgroup G))
      ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom) = ⊥ := by
  apply bot_unique
  intro w hw
  change w = 0
  have he : w.toMul = 1 := by
    by_contra hne
    exact hg (hp g w.toMul hne ((B.mem_naturalSpace w).mp hw.1)
      ((mem_subgroupSpace _ _ w).mp hw.2))
  exact congrArg Additive.ofMul he

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

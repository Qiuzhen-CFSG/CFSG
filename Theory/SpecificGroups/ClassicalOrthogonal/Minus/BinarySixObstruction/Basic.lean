module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Elementary
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.GroupTheory.GroupAction.Iwasawa

/-!
# The binary six-dimensional minus space and its singular points

These are the literal quadratic form and orthogonal commutator group underlying
`ClassicalGroup.POmegaMinus 3 (ZMod 2)`. Over the binary field the nonzero singular
vectors are also the singular projective points. The root subgroup at a point
is the intersection of Omega with the group of Siegel transformations in that
direction. Its definition does not presuppose that the elementary group equals
the commutator group.

This is the geometric setup for the Iwasawa argument for the orthogonal section
in Aschbacher--Smith A.2.15(2), A.2.19 and GLS3 Table 5.3o. Siegel transformations
and their conventions come from `SplitOdd.Siegel` (with its ATLAS attribution).
-/

@[expose] public noncomputable section

namespace ClassicalOrthogonal.Minus.BinarySixObstruction

/-- The field of the exact parameter under consideration. -/
abbrev F := ZMod 2

theorem parameter_binary : parameter F = 1 := by
  have h := parameter_spec F 0
  exact (by decide : ∀ a : F, 0 ≠ a → a = 1) _ (by simpa using h)

/-- Two hyperbolic planes and the chosen anisotropic plane. -/
abbrev NaturalSpace := Space F 2

abbrev naturalForm : QuadraticForm F NaturalSpace := quadraticForm F 3

theorem naturalForm_eq : naturalForm = form F 2 1 := by
  simp only [naturalForm, quadraticForm, parameter_binary]

abbrev FullGroup := Orthogonal F NaturalSpace naturalForm

/-- The actual commutator subgroup, before the scalar quotient. -/
abbrev OmegaGroup := Omega F NaturalSpace naturalForm

/-- Binary singular projective points, represented by their unique nonzero vector. -/
def Point := {v : NaturalSpace // v ≠ 0 ∧ naturalForm v = 0}

instance : Finite Point :=
  inferInstanceAs (Finite {v : NaturalSpace // v ≠ 0 ∧ naturalForm v = 0})

instance pointAction : MulAction OmegaGroup Point where
  smul g p := ⟨g.val.val p.val, by
    refine ⟨fun h => p.prop.1 (g.val.val.injective (h.trans (map_zero _).symm)), ?_⟩
    exact ((Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup naturalForm _).mp
      g.val.prop p.val).trans p.prop.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

@[simp] theorem smul_point_val (g : OmegaGroup) (p : Point) :
    (g • p).val = g.val.val p.val := rfl

theorem card_point : Nat.card Point = 27 := by
  let e : Point ≃ {v : NaturalSpace // v ≠ 0 ∧ form F 2 1 v = 0} :=
    Equiv.subtypeEquivRight (fun v => by rw [naturalForm_eq])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

/-- Parameters perpendicular to the singular direction. -/
abbrev RootParameter (p : Point) := (naturalForm.polarBilin p.val).ker

/-- The additive parameter law is the multiplication law for Siegel transformations. -/
def rootHom (p : Point) : Multiplicative (RootParameter p) →* FullGroup where
  toFun v := siegelElement naturalForm p.val v.toAdd.val p.prop.2 v.toAdd.prop
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact Quadratic.siegel_zero naturalForm p.val x
  map_mul' v w := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact (Quadratic.siegel_add naturalForm p.val v.toAdd.val w.toAdd.val x
      p.prop.2 v.toAdd.prop w.toAdd.prop).symm

/-- The Siegel root subgroup restricted to the actual orthogonal commutator group. -/
def rootSubgroup (p : Point) : Subgroup OmegaGroup :=
  (rootHom p).range.comap (commutator FullGroup).subtype

instance rootSubgroup_commutative (p : Point) : IsMulCommutative (rootSubgroup p) :=
  Subgroup.comap_injective_isMulCommutative _ Subtype.coe_injective

private def singularVectors : Fin 6 → NaturalSpace :=
  ![(![(1,0),(0,0)], (0,0)), (![(0,1),(0,0)], (0,0)),
    (![(0,0),(1,0)], (0,0)), (![(0,0),(0,1)], (0,0)),
    (![(1,1),(0,0)], (1,0)), (![(1,1),(0,0)], (0,1))]

private def spanningPoints (i : Fin 6) : Point := ⟨singularVectors i, by
  rw [naturalForm_eq]
  exact (by decide : ∀ i : Fin 6, singularVectors i ≠ 0 ∧ form F 2 1 (singularVectors i) = 0) i⟩

private theorem singular_expansion (v : NaturalSpace) :
    v = ((v.1 0).1 + v.2.1 + v.2.2) • (spanningPoints 0).val +
      ((v.1 0).2 + v.2.1 + v.2.2) • (spanningPoints 1).val +
      (v.1 1).1 • (spanningPoints 2).val + (v.1 1).2 • (spanningPoints 3).val +
      v.2.1 • (spanningPoints 4).val + v.2.2 • (spanningPoints 5).val := by
  revert v
  decide

/-- The singular points span the natural space, so their action detects every isometry. -/
instance pointAction_faithful : FaithfulSMul OmegaGroup Point where
  eq_of_smul_eq_smul := by
    intro g h he
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hs (i : Fin 6) : g.val.val (spanningPoints i).val =
        h.val.val (spanningPoints i).val := congrArg Subtype.val (he (spanningPoints i))
    rw [singular_expansion v]
    simp only [map_add, map_smul, hs]

end ClassicalOrthogonal.Minus.BinarySixObstruction

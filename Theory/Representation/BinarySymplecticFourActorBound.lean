module
public import Mathlib.RepresentationTheory.Basic
public import Theory.SpecificGroups.PSp4Three.MatrixModel
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
/-!
# Elementary actors on a binary symplectic four-space

A symplectic basis embeds a faithful action preserving a nondegenerate
alternating four-form into the literal Sp₄(2). Its proved two-rank three
bounds every elementary abelian two-subgroup by order eight.

The coordinate argument follows the marked-action construction in
`SymplecticFour/TransvectionRecognition/TraceModelConjugacy.lean`, with
only the form and rank imports needed here. The source application is
Aschbacher--Smith G.11.2(2) and14.3.14--15, printed pp.364 and994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Module Matrix
open scoped IsMulCommutative
namespace Representation
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- Faithful symplectic four-space bounds an elementary binary actor by eight. -/
theorem binarySymplecticFour_elementary_card_le_eight
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 4) (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : B.IsAlt) (hn : B.Nondegenerate)
    (hp : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    (X : Subgroup G) [IsElementaryAbelian 2 X] : Nat.card X ≤ 8 := by
  obtain ⟨e⟩ := Matrix.PSp4Three.exists_isometry 2 B halt hn hd
  let σ : Representation (ZMod 2) G (Matrix.PSp4Three.Vector 2 (ZMod 2)) :=
    e.toLinearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  let f := LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp σ
  have hpres (g : G) : f g ∈ Matrix.symplecticGroup (Fin 2) (ZMod 2) := by
    apply Matrix.PSp4Three.mem_iff_preserves.mpr
    intro v w
    change Matrix.PSp4Three.form ((LinearMap.toMatrix' (σ g)) *ᵥ v)
      ((LinearMap.toMatrix' (σ g)) *ᵥ w) = _
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    change Matrix.PSp4Three.form (e (ρ g (e.symm v))) (e (ρ g (e.symm w))) = _
    rw [e.map_app, hp]
    exact (e.map_app (e.symm w) (e.symm v)).symm.trans (by simp)
  let j : G →* Matrix.symplecticGroup (Fin 2) (ZMod 2) := f.codRestrict _ hpres
  have hj : Function.Injective j := by
    intro a b h
    apply hf
    apply e.toLinearEquiv.conjRingEquiv.injective
    apply LinearMap.toMatrixAlgEquiv'.injective
    exact congrArg Subtype.val h
  have hr : primeRank 2 G ≤ 3 := by
    have he := Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank
      (F := ZMod 2) (n := 1) (by simp) (by decide)
    exact (primeRank_le_of_injective 2 j hj).trans (by simpa using he.le)
  exact (primeRank_le_iff_elementary_card_le G).mp hr X inferInstance
end Representation

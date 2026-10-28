module

public import Theory.SpecificGroups.SymplecticFour.CentralRootLifts
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Torus-compatible root sections in symplectic central extensions

For a finite characteristic-two field of order greater than four, each root
preimage is abelian. Commutating its additive section with a torus element
whose weight differs from one gives a new section. Independence of the
commutator from the chosen lifts makes this section equivariant under the
entire diagonal torus, including arbitrary lifts of its elements.

This is the root-normalization step in the defining-prime multiplier
argument for Sp₄, underlying Aschbacher–Smith I.1.3 (printed p.407),
GLS III §6.1, and the component identification in 13.6.6 (printed p.927).
-/

@[expose] public section

open Matrix
open scoped commutatorElement
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField
variable {F : Type*} [Field F]

def torusWeight (r : Fin 8) (a b : Fˣ) : Fˣ :=
  ![a^2, (a⁻¹)^2, b^2, (b⁻¹)^2, a*b, (a*b)⁻¹, a*b⁻¹, b*a⁻¹] r

theorem diagonal_commute (a b c d : Fˣ) :
    Commute (diagonalTorus a b) (diagonalTorus c d) := by
  apply Subtype.ext
  change (diagonalTorus a b).val * (diagonalTorus c d).val =
    (diagonalTorus c d).val * (diagonalTorus a b).val
  simp only [diagonalTorus, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem diagonal_conjugate (r : Fin 8) (a b : Fˣ) (t : F) :
    diagonalTorus a b * rootElement r t * (diagonalTorus a b)⁻¹ =
      rootElement r ((torusWeight r a b : F) * t) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  ext i j
  change ((diagonalTorus a b).val * (rootElement r t).val) i j =
    ((rootElement r ((torusWeight r a b : F) * t)).val * (diagonalTorus a b).val) i j
  fin_cases r <;>
    simp only [diagonalTorus, Matrix.diagonal_mul, Matrix.mul_diagonal]
  all_goals dsimp [rootElement, rootMatrix, torusWeight]
  all_goals rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks, Matrix.single, pow_two, mul_assoc, mul_comm, mul_left_comm]
  all_goals left; field_simp

variable [Finite F] [CharP F 2]

/-- Root sections can be chosen equivariant for every diagonal torus lift. -/
theorem exists_equivariant_root_lift (hF : 4 < Nat.card F)
    {E : Type*} [Group E] (f : E →* Sp F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (r : Fin 8) :
    ∃ u : Multiplicative F →* E,
      f.comp u = RootSubgroup.parameter r ∧
      ∀ (a b : Fˣ) (z : E), f z = diagonalTorus a b → ∀ t : F,
        z * u (.ofAdd t) * z⁻¹ = u (.ofAdd ((torusWeight r a b : F) * t)) := by
  obtain ⟨u, hu⟩ := CentralRootLifts.exists_root_lift hF f hf hk r
  have hup (x : F) : f (u (.ofAdd x)) = rootElement r x :=
    DFunLike.congr_fun hu (.ofAdd x)
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨c, hc⟩ := exists_ne (1 : Fˣ)
  have hc1 : (c : F) ≠ 1 := fun h => hc (Units.ext h)
  obtain ⟨t, ht⟩ := RootTori.weight_surjective r c
  obtain ⟨A, hA⟩ := hf (RootTori.element r t)
  let d : F := (c : F) - 1
  have hd : d ≠ 0 := sub_ne_zero.mpr hc1
  let s : F → E := fun x => ⁅A, u (.ofAdd (d⁻¹*x))⁆
  have hs (x : F) : f (s x) = rootElement r x := by
    dsimp [s]
    rw [map_commutatorElement, commutatorElement_def, hA, hup,
      RootTori.conjugate, ht]
    have hinv (z : F) : (rootElement r z)⁻¹ = rootElement r (-z) :=
      ((RootSubgroup.parameter (F := F) r).map_inv (.ofAdd z)).symm
    rw [hinv, RootSubgroup.element_add]
    congr 1
    calc
      (c : F) * (d⁻¹ * x) + -(d⁻¹ * x) = d * (d⁻¹ * x) := by dsimp [d]; ring
      _ = x := mul_inv_cancel_left₀ hd x
  have hsadd (x y : F) : s (x+y) = s x * s y := by
    have hcomm : Commute (u (.ofAdd (d⁻¹*x))) (s y) :=
      CentralRootLifts.root_preimage_commute hF f hf hk r
        (by rw [hup]; exact (RootSubgroup.mem_group_iff r _).mpr ⟨_, rfl⟩)
        (by rw [hs]; exact (RootSubgroup.mem_group_iff r _).mpr ⟨_, rfl⟩)
    change ⁅A, u (.ofAdd (d⁻¹*(x+y)))⁆ = _
    rw [mul_add, ofAdd_add, map_mul,
      commutatorElement_mul_right_eq_mul_conj]
    change s x * u (.ofAdd (d⁻¹*x)) * s y * (u (.ofAdd (d⁻¹*x)))⁻¹ = _
    rw [mul_assoc (s x), hcomm.eq, ← mul_assoc,
      mul_assoc (s x * s y), mul_inv_cancel, mul_one]
  refine ⟨{
    toFun x := s x.toAdd
    map_one' := ?_
    map_mul' x y := hsadd x.toAdd y.toAdd }, ?_, ?_⟩
  · simp [s]
  · apply MonoidHom.ext
    intro x
    exact hs x.toAdd
  · intro a b z hz x
    change z * s x * z⁻¹ = s ((torusWeight r a b : F) * x)
    dsimp [s]
    rw [conjugate_commutatorElement]
    apply CentralExtension.commutator_eq_of_image_eq f hk
    · rw [map_mul, map_mul, map_inv, hz, hA]
      have H : Commute (diagonalTorus a b) (RootTori.element r t) :=
        diagonal_commute _ _ _ _
      rw [H.eq, mul_assoc, mul_inv_cancel, mul_one]
    · rw [map_mul, map_mul, map_inv, hz, hup, hup, diagonal_conjugate]
      congr 1
      ring


end Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField

end

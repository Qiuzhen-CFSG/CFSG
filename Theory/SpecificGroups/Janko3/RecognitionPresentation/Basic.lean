module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

/-!
# The ATLAS standard-generator presentation for J₃

We define the eight relators of ATLAS `J3G1-P1` as words in an arbitrary
group, and construct their presented group and evaluation homomorphisms.
Generation gives surjectivity; for a finite presentation, cardinal bounds
then give a multiplicative equivalence between two generated quotients.
Neither finiteness nor a cardinal upper bound for the presentation is asserted
here. In particular, these universal properties are not a recognition theorem.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
The commutator convention is `x⁻¹ * y⁻¹ * x * y`, as in that Magma file.
-/

namespace Sporadic.Janko3.RecognitionPresentation

/-- The eight relators in the ATLAS standard-generator presentation `J3G1-P1`. -/
@[expose] public def relator {G : Type*} [Group G] (x y : G) : Fin 8 → G
  | 0 => x ^ 2
  | 1 => y ^ 3
  | 2 => (x⁻¹ * y⁻¹ * x * y) ^ 9
  | 3 => (x * y) ^ 19
  | 4 => ((x * y) ^ 6 * (x * y⁻¹) ^ 5) ^ 2
  | 5 => ((x * y * x * y * x * y⁻¹) ^ 2 *
      x * y * x * y⁻¹ * x * y⁻¹ * x * y * x * y⁻¹) ^ 2
  | 6 => x * y * x * y * (x * y * x * y⁻¹) ^ 3 *
      x * y * x * y * (x * y * x * y⁻¹) ^ 4 *
      x * y⁻¹ * (x * y * x * y⁻¹) ^ 3
  | 7 => ((x * y) ^ 3 * (x * y * x * y⁻¹) ^ 2) ^ 4

public theorem map_relator {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x y : G) (i : Fin 8) :
    f (relator x y i) = relator (f x) (f y) i := by
  fin_cases i <;> simp only [relator, map_mul, map_inv, map_pow]

/-- These identities alone do not assert either generation or uniqueness. -/
@[expose] public def Satisfies {G : Type*} [Group G] (x y : G) : Prop :=
  ∀ i : Fin 8, relator x y i = 1

/-- A generating pair with the eight specified word identities. -/
@[expose] public def HasGenerators (G : Type*) [Group G] : Prop :=
  ∃ x y : G, Subgroup.closure ({x, y} : Set G) = ⊤ ∧ Satisfies x y

@[expose] public def rels : Set (FreeGroup Bool) :=
  Set.range (relator (FreeGroup.of false) (FreeGroup.of true))

/-- The presented group, without a finiteness or order assumption. -/
public abbrev Presentation := PresentedGroup rels

@[expose] public def x : Presentation := PresentedGroup.of false
@[expose] public def y : Presentation := PresentedGroup.of true

public theorem presentation_satisfies : Satisfies x y := by
  intro i
  change relator ((PresentedGroup.mk rels) (FreeGroup.of false))
    ((PresentedGroup.mk rels) (FreeGroup.of true)) i = 1
  rw [← map_relator (PresentedGroup.mk rels)]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

/-- A pair satisfying the relators induces the specified homomorphism. -/
@[expose] public def evaluation {G : Type*} [Group G] {a b : G}
    (h : Satisfies a b) : Presentation →* G :=
  PresentedGroup.toGroup (f := fun t : Bool => if t then b else a) (by
    rintro r ⟨i, rfl⟩
    rw [map_relator]
    simpa only [FreeGroup.lift_apply_of, Bool.false_eq_true, ↓reduceIte] using h i)

@[simp] public theorem evaluation_x {G : Type*} [Group G] {a b : G}
    (h : Satisfies a b) : evaluation h x = a := by
  exact PresentedGroup.toGroup.of _

@[simp] public theorem evaluation_y {G : Type*} [Group G] {a b : G}
    (h : Satisfies a b) : evaluation h y = b := by
  exact PresentedGroup.toGroup.of _

public theorem evaluation_surjective {G : Type*} [Group G] {a b : G}
    (h : Satisfies a b) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    Function.Surjective (evaluation h) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact ⟨x, evaluation_x h⟩
  · exact ⟨y, evaluation_y h⟩

/-- A finite presentation's upper bound and a generated quotient's lower bound
force the canonical epimorphism to be an isomorphism. -/
public theorem evaluation_bijective_of_card_le {G : Type*} [Group G]
    [Finite Presentation] {a b : G} (h : Satisfies a b)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hcard : Nat.card Presentation ≤ Nat.card G) :
    Function.Bijective (evaluation h) :=
  (evaluation_surjective h hgen).bijective_of_nat_card_le hcard

/-- Two sufficiently large quotients of this finite presentation are isomorphic.
Both maps are induced by the specified generators; the cardinal bounds prove
injectivity, in addition to the surjectivity obtained from generation. -/
public noncomputable def equivOfCardBounds
    {G H : Type*} [Group G] [Group H] [Finite Presentation]
    {a b : G} {c d : H} (hG : Satisfies a b) (hH : Satisfies c d)
    (hgG : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hgH : Subgroup.closure ({c, d} : Set H) = ⊤)
    (hcG : Nat.card Presentation ≤ Nat.card G)
    (hcH : Nat.card Presentation ≤ Nat.card H) : G ≃* H :=
  (MulEquiv.ofBijective (evaluation hG)
    (evaluation_bijective_of_card_le hG hgG hcG)).symm.trans
      (MulEquiv.ofBijective (evaluation hH)
        (evaluation_bijective_of_card_le hH hgH hcH))

public theorem equivOfCardBounds_left
    {G H : Type*} [Group G] [Group H] [Finite Presentation]
    {a b : G} {c d : H} (hG : Satisfies a b) (hH : Satisfies c d)
    (hgG : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hgH : Subgroup.closure ({c, d} : Set H) = ⊤)
    (hcG : Nat.card Presentation ≤ Nat.card G)
    (hcH : Nat.card Presentation ≤ Nat.card H) :
    equivOfCardBounds hG hH hgG hgH hcG hcH a = c := by
  let eG := MulEquiv.ofBijective (evaluation hG)
    (evaluation_bijective_of_card_le hG hgG hcG)
  change (evaluation hH) (eG.symm a) = c
  have he : eG.symm a = x := (eG.symm_apply_eq).mpr (evaluation_x hG).symm
  rw [he, evaluation_x]

public theorem equivOfCardBounds_right
    {G H : Type*} [Group G] [Group H] [Finite Presentation]
    {a b : G} {c d : H} (hG : Satisfies a b) (hH : Satisfies c d)
    (hgG : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hgH : Subgroup.closure ({c, d} : Set H) = ⊤)
    (hcG : Nat.card Presentation ≤ Nat.card G)
    (hcH : Nat.card Presentation ≤ Nat.card H) :
    equivOfCardBounds hG hH hgG hgH hcG hcH b = d := by
  let eG := MulEquiv.ofBijective (evaluation hG)
    (evaluation_bijective_of_card_le hG hgG hcG)
  change (evaluation hH) (eG.symm b) = d
  have he : eG.symm b = y := (eG.symm_apply_eq).mpr (evaluation_y hG).symm
  rw [he, evaluation_y]

end Sporadic.Janko3.RecognitionPresentation

module
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.SpecificGroups.PSL2.BinaryFourFieldExtension
public import GorensteinWalter.LinearRingEquiv

/-!
# Computable coordinates for the canonical sixteen-field extension

The field is a quadratic extension of the existing computable field of four
 elements. Its distinguished root satisfies X⁴+X+1, and quadratic conjugation
is fourth-power Frobenius. Coefficient transport identifies the actual
semilinear group with `Theory.PSL2.BinaryFourFieldExtension.Model`.

The two concrete matrix elements are the coordinates found for the frozen
first local pair of the six-generator J₃ amalgam. Relations, generation, and
marked overlap comparison are separate obligations in subsequent modules.
Source: finite-field uniqueness and the literal coordinate discovery retained
in `Scratch/J3ModelCoordinates/canonical16-coordinates.json`.
-/

@[expose] public section
namespace Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
open QuadraticAlgebra
abbrev Four := Representation.SL2FourNatural.F
abbrev omega : Four := ⟨0, 1⟩
abbrev F := QuadraticAlgebra Four omega 1
instance noRoot : Fact (∀ r : Four, r ^ 2 ≠ omega + 1 * r) := ⟨by decide +kernel⟩
instance : Fintype F := Fintype.ofEquiv (Four × Four) (QuadraticAlgebra.equivProd omega 1).symm
instance : CharP F 2 := charP_of_injective_algebraMap (algebraMap Four F).injective 2
lemma card : Fintype.card F = 16 := by decide +kernel
def z : F := ⟨0,1⟩
lemma z_polynomial : z ^ 4 + z + 1 = 0 := by decide +kernel
lemma star_eq_fourth (x : F) : star x = x ^ 4 := by
  have h : ∀ x : F, star x = x ^ 4 := by decide +kernel
  exact h x
abbrev SL := Matrix.SpecialLinearGroup (Fin 2) F
abbrev Two := Multiplicative (ZMod 2)

def fieldAut : MulAut SL := Theory.PSL2.sl2FieldAut starRingAut
lemma fieldAut_sq : fieldAut * fieldAut = 1 := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  funext i j
  exact star_star (g i j)
private lemma two_cases (a : Two) : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  revert a
  decide +kernel

def action : Two →* MulAut SL where
  toFun a := if a = 1 then 1 else fieldAut
  map_one' := by simp
  map_mul' a b := by
    rcases two_cases a with rfl | rfl <;> rcases two_cases b with rfl | rfl
    · change (1 : MulAut SL) = 1 * 1
      exact (one_mul _).symm
    · change fieldAut = 1 * fieldAut
      exact (one_mul _).symm
    · change fieldAut = fieldAut * 1
      exact (mul_one _).symm
    · change (1 : MulAut SL) = fieldAut * fieldAut
      exact fieldAut_sq.symm
abbrev ComputableModel := SL ⋊[action] Two

def firstMatrix : SL := ⟨!![⟨⟨1,0⟩,⟨1,0⟩⟩, ⟨⟨0,0⟩,⟨0,1⟩⟩; ⟨⟨0,1⟩,⟨0,0⟩⟩, ⟨⟨1,1⟩,⟨1,0⟩⟩], by decide +kernel⟩
def secondMatrix : SL := ⟨!![⟨⟨0,1⟩,⟨1,1⟩⟩, ⟨⟨1,1⟩,⟨0,1⟩⟩; ⟨⟨0,1⟩,⟨1,0⟩⟩, ⟨⟨1,0⟩,⟨1,0⟩⟩], by decide +kernel⟩
def first : ComputableModel := ⟨firstMatrix, 1⟩
def second : ComputableModel := ⟨secondMatrix, Multiplicative.ofAdd 1⟩


noncomputable def fieldEquiv : F ≃+* Theory.PSL2.BinaryField 4 := by
  letI := Fintype.ofFinite (Theory.PSL2.BinaryField 4)
  apply FiniteField.ringEquivOfCardEq
  rw [card, ← Nat.card_eq_fintype_card, Theory.PSL2.BinaryFourFieldExtension.field_card]

noncomputable def linearEquiv : SL ≃* Theory.PSL2.BinaryGroup 4 :=
  (GorensteinWalter.sl2RingEquiv fieldEquiv).trans (Theory.PSL2.sl2QuotientEquiv _)

noncomputable def actorHom : Two →* Theory.PSL2.BinaryFourFieldExtension.Actor where
  toFun a := if a = 1 then 1 else ⟨Theory.PSL2.BinaryFourFieldExtension.fieldInvolution, Subgroup.mem_zpowers _⟩
  map_one' := by simp
  map_mul' a b := by
    rcases two_cases a with rfl | rfl <;> rcases two_cases b with rfl | rfl
    · change (1 : Theory.PSL2.BinaryFourFieldExtension.Actor) = 1 * 1
      exact (one_mul _).symm
    · change _ = 1 * _
      exact (one_mul _).symm
    · change _ = _ * 1
      exact (mul_one _).symm
    · apply Subtype.ext
      change 1 = Theory.PSL2.BinaryFourFieldExtension.fieldInvolution *
        Theory.PSL2.BinaryFourFieldExtension.fieldInvolution
      exact by simpa only [pow_two] using Theory.PSL2.BinaryFourFieldExtension.fieldInvolution_square.symm

private theorem actorHom_injective : Function.Injective actorHom := by
  intro a b he
  rcases two_cases a with rfl | rfl <;> rcases two_cases b with rfl | rfl
  · rfl
  · have hh := congrArg Subtype.val he
    change 1 = Theory.PSL2.BinaryFourFieldExtension.fieldInvolution at hh
    exact (Theory.PSL2.BinaryFourFieldExtension.fieldInvolution_ne_one hh.symm).elim
  · have hh := congrArg Subtype.val he
    change Theory.PSL2.BinaryFourFieldExtension.fieldInvolution = 1 at hh
    exact (Theory.PSL2.BinaryFourFieldExtension.fieldInvolution_ne_one hh).elim
  · rfl

noncomputable def actorEquiv : Two ≃* Theory.PSL2.BinaryFourFieldExtension.Actor :=
  MulEquiv.ofBijective actorHom (by
    have hc : Nat.card Theory.PSL2.BinaryFourFieldExtension.Actor = 2 := by
      rw [Nat.card_zpowers, Theory.PSL2.BinaryFourFieldExtension.fieldInvolution_order]
    have : Finite Theory.PSL2.BinaryFourFieldExtension.Actor :=
      Nat.finite_of_card_ne_zero (by rw [hc]; decide)
    let := Fintype.ofFinite Theory.PSL2.BinaryFourFieldExtension.Actor
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨actorHom_injective, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_zpowers, Theory.PSL2.BinaryFourFieldExtension.fieldInvolution_order]
    simp [Nat.card_eq_fintype_card, Two])

private theorem linearEquiv_fieldAut (g : SL) :
    linearEquiv (fieldAut g) = Theory.PSL2.fieldAut
      Theory.PSL2.BinaryFourFieldExtension.fieldInvolution (linearEquiv g) := by
  change Theory.PSL2.quotientMap _ (GorensteinWalter.sl2RingEquiv fieldEquiv (fieldAut g)) =
    Theory.PSL2.fieldAut Theory.PSL2.BinaryFourFieldExtension.fieldInvolution
      (Theory.PSL2.quotientMap _ (GorensteinWalter.sl2RingEquiv fieldEquiv g))
  rw [Theory.PSL2.fieldAut_apply_quotientMap]
  apply congrArg (Theory.PSL2.quotientMap _)
  apply Subtype.ext
  funext i j
  rw [GorensteinWalter.sl2RingEquiv_apply_entry]
  change fieldEquiv (star (g i j)) =
    Theory.PSL2.BinaryFourFieldExtension.fieldInvolution
      ((GorensteinWalter.sl2RingEquiv fieldEquiv g).val i j)
  rw [GorensteinWalter.sl2RingEquiv_apply_entry]
  rw [star_eq_fourth, map_pow, Theory.PSL2.BinaryFourFieldExtension.fieldInvolution_apply]

noncomputable def modelEquiv : ComputableModel ≃* Theory.PSL2.BinaryFourFieldExtension.Model :=
  SemidirectProduct.congr linearEquiv actorEquiv (by
    intro a
    apply MulEquiv.ext
    intro g
    rcases two_cases a with rfl | rfl
    · simp only [map_one, MulAut.one_apply, MulEquiv.trans_apply]
    · exact linearEquiv_fieldAut g)

end Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates

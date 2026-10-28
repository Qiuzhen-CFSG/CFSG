module
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.MatrixBasics
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.ScalarMarking
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.WeylAction

/-!
# Signed triality roots from two source rank-one pinnings

Start with two actual SL₂ homomorphisms into the same group, over the cubic
field and its actual fixed subfield. Their Weyl images give the positive
root orbits. The length-six braid makes the longest word commute with both
Weyl elements. The two orthogonal-root stabilizers identify its action on
the simple roots with the rank-one sign changes. Conjugation by this longest
word therefore constructs all negative roots and proves the full signed
Weyl table. The third short orbit is reparametrized by one Frobenius, giving
the shifts σ² and σ in the two arm-reflection equations.

The defined rank-one words agree with the images of the literal SL₂ Weyl
matrices, including over the field of two elements. Compatible scalar
transport uses the same extension marking and its restriction to the fixed
subfield throughout.

This is an intermediate source construction. The rank-one pinnings, braid
and orthogonal stabilizers must still be produced on the original quotient;
this module does not derive them or the positive coefficients from 6E(b).
Source: Fong--Seitz II §7 and (9.25), printed pp.218--219; GLS3 2.4.8(e),
with the orbit convention in ScalarMarking.
-/

@[expose] public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
variable {Y : Type*} [Group Y]

structure DihedralPair (Y : Type*) [Group Y] where
  a : Y
  b : Y
  a_sq : a * a = 1
  b_sq : b * b = 1
  braid : (a * b)^6 = 1

namespace DihedralPair
variable (d : DihedralPair Y)
@[simp] theorem a_inv : d.a⁻¹ = d.a := inv_eq_of_mul_eq_one_right d.a_sq
@[simp] theorem b_inv : d.b⁻¹ = d.b := inv_eq_of_mul_eq_one_right d.b_sq

def A : MulAut Y := MulAut.conj d.a
def B : MulAut Y := MulAut.conj d.b
def longest : Y := (d.a*d.b)^3
def W : MulAut Y := MulAut.conj d.longest

@[simp] theorem A_A (x : Y) : d.A (d.A x) = x := by
  change d.a * (d.a*x*d.a⁻¹) * d.a⁻¹ = x
  simp only [d.a_inv]
  calc
    _ = (d.a*d.a)*x*(d.a*d.a) := by group
    _ = x := by rw [d.a_sq]; simp
@[simp] theorem B_B (x : Y) : d.B (d.B x) = x := by
  change d.b * (d.b*x*d.b⁻¹) * d.b⁻¹ = x
  simp only [d.b_inv]
  calc
    _ = (d.b*d.b)*x*(d.b*d.b) := by group
    _ = x := by rw [d.b_sq]; simp

theorem longest_sq : d.longest * d.longest = 1 := by
  simpa only [longest, ← pow_add] using d.braid
@[simp] theorem longest_inv : d.longest⁻¹ = d.longest :=
  inv_eq_of_mul_eq_one_right d.longest_sq

theorem longest_reverse : d.longest = (d.b*d.a)^3 := by
  calc
    d.longest = d.longest⁻¹ := d.longest_inv.symm
    _ = _ := by simp only [longest, ← inv_pow, mul_inv_rev, d.a_inv, d.b_inv]

theorem A_longest : d.A d.longest = d.longest := by
  have hr : d.A (d.a*d.b) = d.b*d.a := by
    change d.a*(d.a*d.b)*d.a⁻¹ = _
    rw [d.a_inv]
    simp only [← mul_assoc, d.a_sq, one_mul]
  change d.A ((d.a*d.b)^3) = d.longest
  rw [map_pow, hr, ← d.longest_reverse]

theorem B_longest : d.B d.longest = d.longest := by
  rw [d.longest_reverse]
  have hr : d.B (d.b*d.a) = d.a*d.b := by
    change d.b*(d.b*d.a)*d.b⁻¹ = _
    rw [d.b_inv]
    simp only [← mul_assoc, d.b_sq, one_mul]
  rw [map_pow, hr]
  exact d.longest_reverse

@[simp] theorem W_W (x : Y) : d.W (d.W x) = x := by
  change d.longest*(d.longest*x*d.longest⁻¹)*d.longest⁻¹ = x
  rw [d.longest_inv]
  calc
    _ = (d.longest*d.longest)*x*(d.longest*d.longest) := by group
    _ = x := by rw [d.longest_sq]; simp

theorem A_W (x : Y) : d.A (d.W x) = d.W (d.A x) := by
  change d.A (d.longest*x*d.longest⁻¹) = d.longest*d.A x*d.longest⁻¹
  rw [map_mul, map_mul, map_inv, d.A_longest]
theorem B_W (x : Y) : d.B (d.W x) = d.W (d.B x) := by
  change d.B (d.longest*x*d.longest⁻¹) = d.longest*d.B x*d.longest⁻¹
  rw [map_mul, map_mul, map_inv, d.B_longest]

theorem W_apply (x : Y) :
    d.W x = d.A (d.B (d.A (d.B (d.A (d.B x))))) := by
  simp only [W, A, B, MulAut.conj_apply, longest, pow_succ, pow_zero]
  group

theorem W_apply_reverse (x : Y) :
    d.W x = d.B (d.A (d.B (d.A (d.B (d.A x))))) := by
  change d.longest*x*d.longest⁻¹ = _
  rw [d.longest_reverse]
  simp only [A, B, MulAut.conj_apply, pow_succ, pow_zero]
  group

theorem W_eq_A (x : Y) (hx : d.B (d.A (d.B x)) = d.A (d.B x)) :
    d.W x = d.A x := by
  rw [d.W_apply, hx, d.A_A, d.B_B]
theorem W_eq_B (x : Y) (hx : d.A (d.B (d.A x)) = d.B (d.A x)) :
    d.W x = d.B x := by
  rw [d.W_apply_reverse, hx, d.B_B, d.A_A]
end DihedralPair

open Theory.PSL2.SemilinearCoverage
variable {F : Type*} [Field F] [CharP F 2]

theorem weyl_root_word :
    uni (1 : F) * (weyl F * uni 1 * (weyl F)⁻¹) * uni 1 = weyl F := by
  have hw : (weyl F)⁻¹ = weyl F := inv_eq_of_mul_eq_one_right weyl_sq
  rw [hw]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Theory.PSL2.SemilinearCoverage
open Triality.Standard Triality.Standard.RootPresentationRecognition
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y] {σ : F ≃+* F}
local notation "K" => ScalarMarking.SourceFixed (σ := σ)

/-- Two actual rank-one maps in the same group.  The remaining geometric
premises are the length-six braid and the two orthogonal-root stabilizers. -/
structure RankOnePair (σ : F ≃+* F) (Y : Type*) [Group Y] where
  shortMap : SL2 F →* Y
  longMap : SL2 (ScalarMarking.SourceFixed (σ := σ)) →* Y
  braid : (shortMap (weyl F) * longMap (weyl _)) ^ 6 = 1
  orthogonalShort : ∀ t : F,
    MulAut.conj (longMap (weyl _))
      (MulAut.conj (shortMap (weyl F))
        (MulAut.conj (longMap (weyl _)) (shortMap (uni t)))) =
      MulAut.conj (shortMap (weyl F))
        (MulAut.conj (longMap (weyl _)) (shortMap (uni t)))
  orthogonalLong : ∀ t : ScalarMarking.SourceFixed (σ := σ),
    MulAut.conj (shortMap (weyl F))
      (MulAut.conj (longMap (weyl _))
        (MulAut.conj (shortMap (weyl F)) (longMap (uni t)))) =
      MulAut.conj (longMap (weyl _))
        (MulAut.conj (shortMap (weyl F)) (longMap (uni t)))

namespace RankOnePair
variable (p : RankOnePair σ Y)

def dihedral : DihedralPair Y where
  a := p.shortMap (weyl F)
  b := p.longMap (weyl K)
  a_sq := by rw [← map_mul, weyl_sq, map_one]
  b_sq := by rw [← map_mul, weyl_sq, map_one]
  braid := p.braid

def shortBase : Multiplicative F →* Y :=
  p.shortMap.comp (Matrix.SpecialLinearGroup.upperUnipotentHom F)
def longBase : Multiplicative K →* Y :=
  p.longMap.comp (Matrix.SpecialLinearGroup.upperUnipotentHom K)

def shortOrbit : Fin 3 → Multiplicative F →* Y :=
  ![p.shortBase, p.dihedral.B.toMonoidHom.comp p.shortBase,
    p.dihedral.A.toMonoidHom.comp (p.dihedral.B.toMonoidHom.comp p.shortBase)]
def longOrbit : Fin 3 → Multiplicative K →* Y :=
  ![p.longBase, p.dihedral.A.toMonoidHom.comp p.longBase,
    p.dihedral.B.toMonoidHom.comp (p.dihedral.A.toMonoidHom.comp p.longBase)]

abbrev s (i : Fin 3) (t : F) : Y := p.shortOrbit i (.ofAdd t)
abbrev l (i : Fin 3) (t : K) : Y := p.longOrbit i (.ofAdd t)

@[simp] theorem s_zero (t : F) : p.s 0 t = p.shortMap (uni t) := rfl
@[simp] theorem l_zero (t : K) : p.l 0 t = p.longMap (uni t) := rfl
@[simp] theorem s_one (t : F) : p.s 1 t = p.dihedral.B (p.s 0 t) := rfl
@[simp] theorem s_two (t : F) : p.s 2 t = p.dihedral.A (p.s 1 t) := rfl
@[simp] theorem l_one (t : K) : p.l 1 t = p.dihedral.A (p.l 0 t) := rfl
@[simp] theorem l_two (t : K) : p.l 2 t = p.dihedral.B (p.l 1 t) := rfl

theorem W_shortBase (t : F) : p.dihedral.W (p.s 0 t) = p.dihedral.A (p.s 0 t) :=
  p.dihedral.W_eq_A _ (p.orthogonalShort t)
theorem W_longBase (t : K) : p.dihedral.W (p.l 0 t) = p.dihedral.B (p.l 0 t) :=
  p.dihedral.W_eq_B _ (p.orthogonalLong t)

/-- Negatives are conjugates by the source longest word. -/
def signedValue (positive : Bool) (x : Y) : Y := if positive then x else p.dihedral.W x

theorem A_signedValue (positive : Bool) (x : Y) :
    p.dihedral.A (p.signedValue positive x) = p.signedValue positive (p.dihedral.A x) := by
  cases positive
  · exact p.dihedral.A_W x
  · rfl

theorem B_signedValue (positive : Bool) (x : Y) :
    p.dihedral.B (p.signedValue positive x) = p.signedValue positive (p.dihedral.B x) := by
  cases positive
  · exact p.dihedral.B_W x
  · rfl

theorem A_shortBase (positive : Bool) (t : F) :
    p.dihedral.A (p.signedValue positive (p.s 0 t)) =
      p.signedValue (!positive) (p.s 0 t) := by
  rw [p.A_signedValue, ← p.W_shortBase]
  cases positive
  · exact p.dihedral.W_W _
  · rfl

theorem B_longBase (positive : Bool) (t : K) :
    p.dihedral.B (p.signedValue positive (p.l 0 t)) =
      p.signedValue (!positive) (p.l 0 t) := by
  rw [p.B_signedValue, ← p.W_longBase]
  cases positive
  · exact p.dihedral.W_W _
  · rfl

theorem A_shortOne (positive : Bool) (t : F) :
    p.dihedral.A (p.signedValue positive (p.s 1 t)) =
      p.signedValue positive (p.s 2 t) := p.A_signedValue _ _

theorem A_shortTwo (positive : Bool) (t : F) :
    p.dihedral.A (p.signedValue positive (p.s 2 t)) =
      p.signedValue positive (p.s 1 t) := by
  rw [p.A_signedValue, p.s_two, p.dihedral.A_A]

theorem A_long (positive : Bool) (i : Fin 3) (t : K) :
    p.dihedral.A (p.signedValue positive (p.l i t)) =
      p.signedValue positive (p.l (![1,0,2] i) t) := by
  rw [p.A_signedValue]
  apply congrArg (p.signedValue positive)
  fin_cases i
  · rfl
  · exact p.dihedral.A_A _
  · exact p.orthogonalLong t

theorem B_short (positive : Bool) (i : Fin 3) (t : F) :
    p.dihedral.B (p.signedValue positive (p.s i t)) =
      p.signedValue positive (p.s (![1,0,2] i) t) := by
  rw [p.B_signedValue]
  apply congrArg (p.signedValue positive)
  fin_cases i
  · rfl
  · exact p.dihedral.B_B _
  · exact p.orthogonalShort t

theorem B_longOne (positive : Bool) (t : K) :
    p.dihedral.B (p.signedValue positive (p.l 1 t)) =
      p.signedValue positive (p.l 2 t) := p.B_signedValue _ _

theorem B_longTwo (positive : Bool) (t : K) :
    p.dihedral.B (p.signedValue positive (p.l 2 t)) =
      p.signedValue positive (p.l 1 t) := by
  rw [p.B_signedValue, p.l_two, p.dihedral.B_B]

/-- The orbit marking on the third short root is shifted by one Frobenius. -/
def markedShort (i : Fin 3) : Multiplicative F →* Y :=
  if i = 2 then (p.shortOrbit i).comp σ.toRingHom.toAddMonoidHom.toMultiplicative
  else p.shortOrbit i

@[simp] theorem markedShort_zero (t : F) : p.markedShort 0 (.ofAdd t) = p.s 0 t := rfl
@[simp] theorem markedShort_one (t : F) : p.markedShort 1 (.ofAdd t) = p.s 1 t := rfl
@[simp] theorem markedShort_two (t : F) : p.markedShort 2 (.ofAdd t) = p.s 2 (σ t) := rfl

variable {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)

/-- Signed roots are constructed from the two same-source rank-one maps. -/
def signedRoots : SignedRoots (n := n) (hn := hn) Y where
  positive := e.positiveRoots p.markedShort p.longOrbit
  negativeShort i := p.dihedral.W.toMonoidHom.comp
    ((p.markedShort i).comp e.extension.symm.toRingHom.toAddMonoidHom.toMultiplicative)
  negativeLong i := p.dihedral.W.toMonoidHom.comp
    ((p.longOrbit i).comp e.fixed.symm.toRingHom.toAddMonoidHom.toMultiplicative)

@[simp] theorem signedRoots_short (positive : Bool) (i : Fin 3) (t : F) :
    (p.signedRoots e).shortSigned positive i (e.extension t) =
      p.signedValue positive (p.markedShort i (.ofAdd t)) := by
  cases positive <;>
    simp [signedRoots, SignedRoots.shortSigned, SignedRoots.shortValue,
      SignedRoots.negativeShortValue, signedValue, e.positiveRoots_short]

@[simp] theorem signedRoots_long (positive : Bool) (i : Fin 3) (t : K) :
    (p.signedRoots e).longSigned positive i (e.fixed t) =
      p.signedValue positive (p.l i t) := by
  cases positive <;>
    simp [signedRoots, SignedRoots.longSigned, SignedRoots.longValue,
      SignedRoots.negativeLongValue, signedValue, e.positiveRoots_long]

theorem nA_one : (p.signedRoots e).nA 1 = p.dihedral.a := by
  have hp : (p.signedRoots e).shortValue 0 1 = p.s 0 1 := by
    simpa [SignedRoots.shortSigned, signedValue] using p.signedRoots_short e true 0 1
  have hn : (p.signedRoots e).negativeShortValue 0 1 = p.dihedral.W (p.s 0 1) := by
    simpa [SignedRoots.shortSigned, signedValue] using p.signedRoots_short e false 0 1
  simp only [SignedRoots.nA, inv_one, Units.val_one, hp, hn, p.W_shortBase]
  change p.shortMap (uni 1) *
    (p.shortMap (weyl F) * p.shortMap (uni 1) * (p.shortMap (weyl F))⁻¹) *
      p.shortMap (uni 1) = p.shortMap (weyl F)
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, weyl_root_word]

theorem nB_one : (p.signedRoots e).nB 1 = p.dihedral.b := by
  have hp : (p.signedRoots e).longValue 0 1 = p.l 0 1 := by
    simpa [SignedRoots.longSigned, signedValue] using p.signedRoots_long e true 0 1
  have hn : (p.signedRoots e).negativeLongValue 0 1 = p.dihedral.W (p.l 0 1) := by
    simpa [SignedRoots.longSigned, signedValue] using p.signedRoots_long e false 0 1
  simp only [SignedRoots.nB, inv_one, Units.val_one, hp, hn, p.W_longBase]
  change p.longMap (uni 1) *
    (p.longMap (weyl K) * p.longMap (uni 1) * (p.longMap (weyl K))⁻¹) *
      p.longMap (uni 1) = p.longMap (weyl K)
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, weyl_root_word]

/-- The two original Weyl involutions give the complete signed action table;
the Frobenius shifts survive in characteristic two. -/
theorem actions : (p.signedRoots e).ActionRelations where
  arms_short0 positive t := by
    obtain ⟨t,rfl⟩ := e.extension.surjective t
    rw [p.nA_one, p.signedRoots_short, p.signedRoots_short, p.markedShort_zero]
    exact p.A_shortBase positive t
  arms_short1 positive t := by
    obtain ⟨t,rfl⟩ := e.extension.surjective t
    rw [p.nA_one, ← e.frobenius, ← e.frobenius,
      p.signedRoots_short, p.signedRoots_short,
      p.markedShort_one, p.markedShort_two, e.cubic]
    exact p.A_shortOne positive t
  arms_short2 positive t := by
    obtain ⟨t,rfl⟩ := e.extension.surjective t
    rw [p.nA_one, ← e.frobenius, p.signedRoots_short, p.signedRoots_short,
      p.markedShort_two, p.markedShort_one]
    exact p.A_shortTwo positive (σ t)
  arms_long positive i t := by
    obtain ⟨t,rfl⟩ := e.fixed.surjective t
    rw [p.nA_one, p.signedRoots_long, p.signedRoots_long]
    exact p.A_long positive i t
  central_short positive i t := by
    obtain ⟨t,rfl⟩ := e.extension.surjective t
    rw [p.nB_one, p.signedRoots_short, p.signedRoots_short]
    fin_cases i
    · exact p.B_short positive 0 t
    · exact p.B_short positive 1 t
    · exact p.B_short positive 2 (σ t)
  central_long0 positive t := by
    obtain ⟨t,rfl⟩ := e.fixed.surjective t
    rw [p.nB_one, p.signedRoots_long, p.signedRoots_long]
    exact p.B_longBase positive t
  central_long1 positive t := by
    obtain ⟨t,rfl⟩ := e.fixed.surjective t
    rw [p.nB_one, p.signedRoots_long, p.signedRoots_long]
    exact p.B_longOne positive t
  central_long2 positive t := by
    obtain ⟨t,rfl⟩ := e.fixed.surjective t
    rw [p.nB_one, p.signedRoots_long, p.signedRoots_long]
    exact p.B_longTwo positive t

/-- The source braid and rank-one involutions also hold for the defined words. -/
theorem weylRelations (h : (p.signedRoots e).positive.Relations) :
    (p.signedRoots e).WeylRelations where
  positiveRelations := h
  nA_sq := by rw [p.nA_one, pow_two]; exact p.dihedral.a_sq
  nB_sq := by rw [p.nB_one, pow_two]; exact p.dihedral.b_sq
  braid := by rw [p.nA_one, p.nB_one]; exact p.dihedral.braid

end RankOnePair
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource


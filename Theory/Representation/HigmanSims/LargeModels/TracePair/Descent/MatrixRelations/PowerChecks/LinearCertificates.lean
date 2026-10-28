module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Packed
/-!
# Structural certificates for packed matrix products

A certificate is built from the actual images of coordinate basis rows using
addition and multiplication by omega. Its two natural-number planes are then
checked against the requested input and output. Linearity proves the decoded
matrix identity, without extracting every coefficient of a dense packed row.

This interface is used for the literal HSG1-f4r896aB0 power relations. See
`TracePair/source/README.md` for the original ATLAS data and field convention.
The generating programs propose certificates; Lean checks every arithmetic
identity and the soundness of every certificate constructor.
-/

open Representation.HigmanSims.LargeModels.TracePair
open Certificates Packed
open scoped Matrix
@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.LinearCertificates
variable {n : ℕ}
def vec (a : Row) : Fin n → Four := fun j => decode a j.val
def Good (b : Mat) (a c : Row) : Prop := vec (n := n) a ᵥ* eval n b = vec c

theorem vec_add (a b : Row) : vec (n := n) (Base.addRow a b) = vec a + vec b := by
  funext j
  exact Base.entry_add omega a b j.val

theorem vec_t (a : Row) : vec (n := n) (Base.timesT a) = omega • vec a := by
  funext j
  exact Base.entry_timesT omega omega_sq a j.val

theorem good_add (b : Mat) (a c a' c' : Row)
    (h : Good (n := n) b a c) (h' : Good (n := n) b a' c') :
    Good (n := n) b (Base.addRow a a') (Base.addRow c c') := by
  unfold Good at *
  rw [vec_add, vec_add, Matrix.add_vecMul, h, h']

theorem good_t (b : Mat) (a c : Row) (h : Good (n := n) b a c) :
    Good (n := n) b (Base.timesT a) (Base.timesT c) := by
  unfold Good at *
  rw [vec_t, vec_t, Matrix.smul_vecMul, h]

theorem vec_basis (i : Fin n) : vec (2 ^ i.val, 0) = Pi.single i (1 : Four) := by
  funext j
  simp [vec, decode, Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
    Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]

theorem good_basis (b : Mat) (i : Fin n) : Good (n := n) b (2 ^ i.val, 0) (b.getD i.val (0,0)) := by
  unfold Good
  rw [vec_basis, Matrix.single_vecMul]
  rw [one_smul]
  rfl

structure Cert (b : Mat) where
  input : Row
  output : Row
  sound : Good (n := n) b input output

def basis (b : Mat) (i : Fin n) : Cert (n := n) b :=
  ⟨(2 ^ i.val, 0), b.getD i.val (0,0), good_basis b i⟩
def add {b : Mat} (x y : Cert (n := n) b) : Cert (n := n) b :=
  ⟨Base.addRow x.input y.input, Base.addRow x.output y.output, good_add b _ _ _ _ x.sound y.sound⟩
def t {b : Mat} (x : Cert (n := n) b) : Cert (n := n) b :=
  ⟨Base.timesT x.input, Base.timesT x.output, good_t b _ _ x.sound⟩

def zero (b : Mat) : Cert (n := n) b :=
  ⟨(0,0), (0,0), by
    unfold Good vec
    simp only [decode, Base.entry_zero]
    exact Matrix.zero_vecMul _⟩

theorem of_certificate {b : Mat} (c : Cert (n := n) b) (a d : Row)
    (ha : c.input = a) (hd : c.output = d) : Good (n := n) b a d := by
  rw [← ha, ← hd]
  exact c.sound

theorem eval_product (a b c : Mat)
    (h : ∀ i : Fin n, Good (n := n) b (a.getD i.val (0,0)) (c.getD i.val (0,0))) :
    Packed.eval n a * Packed.eval n b = Packed.eval n c := by
  funext i j
  exact congrFun (h i) j

theorem eval_inverse (a b : Mat)
    (h : ∀ i : Fin n, Good (n := n) b (a.getD i.val (0,0)) (2 ^ i.val, 0)) :
    Packed.eval n a * Packed.eval n b = 1 := by
  funext i j
  calc
    (Packed.eval n a * Packed.eval n b) i j = vec (n := n) (2 ^ i.val, 0) j :=
      congrFun (h i) j
    _ = (1 : Matrix (Fin n) (Fin n) Four) i j := by
      rw [vec_basis]
      simp only [Pi.single_apply, Matrix.one_apply, eq_comm]

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.LinearCertificates

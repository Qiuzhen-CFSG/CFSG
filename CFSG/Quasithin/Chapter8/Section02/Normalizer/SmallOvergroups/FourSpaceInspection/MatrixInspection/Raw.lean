module

public import Theory.Representation.BinaryPermutationMulAction
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.BitVec
public import Mathlib.Data.Fintype.Vector

/-!
# Binary columns for the marked four-space inspection

The sixteen bit strings encode the additive group of the four-dimensional
binary space, low bit first. Every additive automorphism is determined by
its four basis images. The faithful action on bit strings lets small checked
function identities imply identities of the actual automorphisms.

These coordinates match the saved search for the overgroup inspection in
Aschbacher–Smith, proof of 8.2.8(1), printed p.719/PDF p.736.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection
abbrev Bits := BitVec 4
instance bitsFintype : Fintype Bits :=
  Fintype.ofEquiv (Fin 16) (BitVec.equivFin (m := 4)).toEquiv.symm

abbrev Columns := Fin 4 → Bits
abbrev Vector := Multiplicative (Fin 4 → ZMod 2)

def basisBits : Fin 4 → Bits := ![1, 2, 4, 8]
def applyMatrix (c : Columns) : Function.End Bits := fun x =>
  (if x.getLsb 0 then c 0 else 0) ^^^
  (if x.getLsb 1 then c 1 else 0) ^^^
  (if x.getLsb 2 then c 2 else 0) ^^^
  (if x.getLsb 3 then c 3 else 0)
def decode (x : Bits) : Vector :=
  Multiplicative.ofAdd fun i => if x.getLsb i then 1 else 0

theorem decode_bijective : Function.Bijective decode := by decide +kernel

theorem decode_zero : decode 0 = 1 := by decide +kernel

theorem decode_xor : ∀ x y, decode (x ^^^ y) = decode x * decode y := by
  decide +kernel

theorem decode_basis : ∀ x, decode x =
    (if x.getLsb 0 then decode (basisBits 0) else 1) *
    (if x.getLsb 1 then decode (basisBits 1) else 1) *
    (if x.getLsb 2 then decode (basisBits 2) else 1) *
    (if x.getLsb 3 then decode (basisBits 3) else 1) := by decide +kernel

theorem decode_applyMatrix (c : Columns) (x : Bits) : decode (applyMatrix c x) =
    (if x.getLsb 0 then decode (c 0) else 1) *
    (if x.getLsb 1 then decode (c 1) else 1) *
    (if x.getLsb 2 then decode (c 2) else 1) *
    (if x.getLsb 3 then decode (c 3) else 1) := by
  simp only [applyMatrix, decode_xor, apply_ite decode, decode_zero]

noncomputable def bitEquiv : Bits ≃ Vector := Equiv.ofBijective decode decode_bijective
noncomputable def columns (f : MulAut Vector) : Columns :=
  fun i => bitEquiv.symm (f (decode (basisBits i)))

theorem aut_apply_decode (f : MulAut Vector) (x : Bits) :
    f (decode x) = decode (applyMatrix (columns f) x) := by
  rw [decode_applyMatrix]
  conv_lhs => rw [decode_basis x]
  simp only [map_mul, apply_ite f, map_one]
  have h (i) : decode (columns f i) = f (decode (basisBits i)) :=
    bitEquiv.apply_symm_apply _
  simp only [h]

def expandedBits (x : Bits) : Fin 5 → Bool :=
  ![x.getLsb 0, x.getLsb 1, x.getLsb 2, x.getLsb 3,
    x.getLsb 0 ^^ x.getLsb 1 ^^ x.getLsb 2 ^^ x.getLsb 3]
def fromBits (b : Fin 4 → Bool) : Bits :=
  (BitVec.ofBoolListLE (List.ofFn b)).cast (by simp)

theorem decode_fromBits : ∀ b, (decode (fromBits b)).toAdd =
    fun i => if b i then 1 else 0 := by decide +kernel

def permuteBits (σ : Equiv.Perm (Fin 5)) : Function.End Bits := fun x =>
  fromBits fun i => expandedBits x (σ.symm i.castSucc)


/-- The faithful action on the sixteen binary coordinate strings. -/
noncomputable def bitAction : MulAut Vector →* Function.End Bits where
  toFun f x := bitEquiv.symm (f (decode x))
  map_one' := by
    funext x
    exact bitEquiv.symm_apply_apply x
  map_mul' f g := by
    funext x
    change bitEquiv.symm (f (g (decode x))) =
      bitEquiv.symm (f (decode (bitEquiv.symm (g (decode x)))))
    rw [show decode (bitEquiv.symm (g (decode x))) = g (decode x) from
      bitEquiv.apply_symm_apply _]

theorem bitAction_injective : Function.Injective bitAction := by
  intro f g h
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := decode_bijective.surjective v
  have hx := congrArg decode (congrFun h x)
  change bitEquiv (bitEquiv.symm (f (decode x))) =
    bitEquiv (bitEquiv.symm (g (decode x))) at hx
  simpa only [bitEquiv.apply_symm_apply] using hx

/-- Every automorphism is determined by four columns, in the certificate convention. -/
theorem bitAction_eq_applyMatrix (f : MulAut Vector) :
    bitAction f = applyMatrix (columns f) := by
  funext x
  change bitEquiv.symm (f (decode x)) = _
  rw [aut_apply_decode]
  exact bitEquiv.symm_apply_apply _

theorem applyMatrix_columns_injective (f : MulAut Vector) :
    Function.Injective (applyMatrix (columns f)) := by
  intro x y h
  apply decode_bijective.injective
  apply f.injective
  rw [aut_apply_decode, aut_apply_decode, h]

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection

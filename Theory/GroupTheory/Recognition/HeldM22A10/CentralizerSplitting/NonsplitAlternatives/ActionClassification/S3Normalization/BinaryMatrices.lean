module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.Coordinates
public import Mathlib.Data.Fin.Init
/-!
# Binary matrices for labelled S₃ normalization

Four columns with entries in `Fin 16` encode endomorphisms of the binary
four-space. XOR is transported to its actual group multiplication, and a
trivial matrix kernel constructs a multiplicative equivalence by finiteness.
Composition and the three model operators are identified with their column
formulas. These are computational coordinates for the elementary S₃ step
supporting Huppert–Blackburn, *Finite Groups III*, XII.1.18(b), p.314.
-/

open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization.BinaryMatrices

public section
abbrev Code := Fin 16
abbrev Mat := Code × Code × Code × Code

@[expose] def decode (v : Code) : BinaryFour := Multiplicative.ofAdd
  ![(v.val % 2 : ℕ), (v.val / 2 % 2 : ℕ), (v.val / 4 % 2 : ℕ), (v.val / 8 % 2 : ℕ)]
@[expose] def encode (v : BinaryFour) : Code :=
  Fin.ofNat 16 ((v.toAdd 0).val + 2 * (v.toAdd 1).val + 4 * (v.toAdd 2).val + 8 * (v.toAdd 3).val)

theorem encode_decode : ∀ v, encode (decode v) = v := by decide +kernel
theorem decode_encode : ∀ v, decode (encode v) = v := by decide +kernel
theorem decode_xor : ∀ v w, decode (v ^^^ w) = decode v * decode w := by decide +kernel
theorem decode_zero : decode 0 = 1 := by decide +kernel

@[expose] def app (m : Mat) (v : Code) : Code :=
  (if v.val % 2 = 1 then m.1 else 0) ^^^
  (if v.val / 2 % 2 = 1 then m.2.1 else 0) ^^^
  (if v.val / 4 % 2 = 1 then m.2.2.1 else 0) ^^^
  (if v.val / 8 % 2 = 1 then m.2.2.2 else 0)
@[expose] def cols (m : Mat) : Fin 4 → Code := ![m.1, m.2.1, m.2.2.1, m.2.2.2]
@[expose] def mat (m : Mat) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun j i => (decode (cols m i)).toAdd j
@[expose] def lin (m : Mat) : BinaryFour →* BinaryFour where
  toFun := fun v => Multiplicative.ofAdd ((mat m).mulVec v.toAdd)
  map_one' := by
    change Multiplicative.ofAdd ((mat m).mulVec 0) = 1
    rw [Matrix.mulVec_zero]
    rfl
  map_mul' v w := congrArg Multiplicative.ofAdd (Matrix.mulVec_add _ _ _)

theorem lin_basis (m : Mat) (i : Fin 4) : lin m (binaryBasis i) = decode (cols m i) := by
  change Multiplicative.ofAdd ((mat m).mulVec (Pi.single i 1)) = _
  rw [Matrix.mulVec_single_one]
  rfl

theorem lin_decode (m : Mat) (v : Code) : lin m (decode v) = decode (app m v) := by
  have expansion : ∀ w : Code, decode w =
      binaryBasis 0 ^ (w.val % 2) * binaryBasis 1 ^ (w.val / 2 % 2) *
      binaryBasis 2 ^ (w.val / 4 % 2) * binaryBasis 3 ^ (w.val / 8 % 2) := by
    decide +kernel
  rw [expansion]
  simp only [map_mul, map_pow, lin_basis]
  fin_cases v <;> norm_num [app, decode_xor, decode_zero, cols] <;> rfl

@[expose] def ident : Mat := (1,2,4,8)
@[expose] def cubic : Mat := (2,4,1,8)
@[expose] def comp (m n : Mat) : Mat := (app m n.1, app m n.2.1, app m n.2.2.1, app m n.2.2.2)
@[expose] def trivialKernel (m : Mat) : Prop := ∀ v : Code, app m v = 0 → v = 0
instance (m : Mat) : Decidable (trivialKernel m) := inferInstanceAs (Decidable (∀ _, _))

theorem decode_injective : Function.Injective decode := by
  intro v w h
  simpa only [encode_decode] using congrArg encode h

theorem cols_comp (m n : Mat) (i : Fin 4) : cols (comp m n) i = app m (cols n i) := by
  fin_cases i <;> rfl

theorem hom_ext (f g : BinaryFour →* BinaryFour)
    (h : ∀ i, f (binaryBasis i) = g (binaryBasis i)) : f = g := by
  apply MonoidHom.ext
  intro v
  conv_lhs => rw [binaryBasis_expansion v]
  conv_rhs => rw [binaryBasis_expansion v]
  simp only [map_prod, map_pow, h]

theorem lin_comp (m n : Mat) : lin (comp m n) = (lin m).comp (lin n) := by
  apply hom_ext
  intro i
  simp only [MonoidHom.comp_apply, lin_basis, lin_decode, cols_comp]

theorem lin_injective : Function.Injective lin := by
  intro m n h
  have hb (i : Fin 4) := congrArg (fun f : BinaryFour →* BinaryFour => f (binaryBasis i)) h
  simp only [lin_basis] at hb
  have hc (i : Fin 4) := decode_injective (hb i)
  exact Prod.ext (hc 0) (Prod.ext (hc 1) (Prod.ext (hc 2) (hc 3)))

theorem lin_ident : lin ident = MonoidHom.id BinaryFour := by
  apply hom_ext
  intro i
  rw [lin_basis]
  change decode (cols ident i) = binaryBasis i
  have h : ∀ i, decode (cols ident i) = binaryBasis i := by decide +kernel
  exact h i

@[expose] def ofAut (f : MulAut BinaryFour) : Mat :=
  (encode (f (binaryBasis 0)), encode (f (binaryBasis 1)),
    encode (f (binaryBasis 2)), encode (f (binaryBasis 3)))

theorem lin_ofAut (f : MulAut BinaryFour) : lin (ofAut f) = f.toMonoidHom := by
  apply hom_ext
  intro i
  rw [lin_basis]
  fin_cases i <;> exact decode_encode _

theorem lin_ker (m : Mat) (h : trivialKernel m) : Function.Injective (lin m) := by
  apply (lin m).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro v hv
  change v = 1
  change lin m v = 1 at hv
  have hv' : app m (encode v) = 0 := by
    apply decode_injective
    rw [← lin_decode, decode_encode, hv, decode_zero]
  have := h (encode v) hv'
  rw [← decode_encode v, this, decode_zero]

@[expose] noncomputable def aut (m : Mat) (h : trivialKernel m) : MulAut BinaryFour :=
  MulEquiv.ofBijective (lin m) ⟨lin_ker m h, Finite.injective_iff_surjective.mp (lin_ker m h)⟩

theorem aut_apply (m : Mat) (h : trivialKernel m) (v : BinaryFour) :
    aut m h v = lin m v := rfl


/-- The standard coordinate codes decode to the existing labelled basis. -/
theorem decode_basis (i : Fin 4) : decode (cols ident i) = binaryBasis i := by
  have h : ∀ i, decode (cols ident i) = binaryBasis i := by decide +kernel
  exact h i

theorem app_basis (m : Mat) (i : Fin 4) : app m (cols ident i) = cols m i := by
  apply decode_injective
  rw [← lin_decode, decode_basis, lin_basis]

theorem ofAut_mul (f g : MulAut BinaryFour) :
    ofAut (f * g) = comp (ofAut f) (ofAut g) := by
  apply lin_injective
  rw [lin_comp, lin_ofAut, lin_ofAut, lin_ofAut]
  rfl

theorem ofAut_one : ofAut (1 : MulAut BinaryFour) = ident := by
  apply lin_injective
  rw [lin_ofAut, lin_ident]
  rfl

theorem ofAut_injective : Function.Injective ofAut := by
  intro f g h
  have he := congrArg lin h
  rw [lin_ofAut, lin_ofAut] at he
  apply MulEquiv.ext
  intro v
  exact congrArg (fun h : BinaryFour →* BinaryFour => h v) he

@[expose] def ordinary : Mat := (2,1,4,8)
@[expose] def twisted : Mat := (13,14,11,7)

theorem ofAut_cubic : ofAut (permutationAction threeCycle) = cubic := by decide +kernel
theorem ofAut_ordinary : ofAut (permutationAction transposition) = ordinary := by decide +kernel
theorem ofAut_twisted : ofAut (twistedAction transposition) = twisted := by decide +kernel

theorem lin_cubic : lin cubic = (permutationAction threeCycle).toMonoidHom := by
  rw [← ofAut_cubic, lin_ofAut]
theorem lin_ordinary : lin ordinary = (permutationAction transposition).toMonoidHom := by
  rw [← ofAut_ordinary, lin_ofAut]
theorem lin_twisted : lin twisted = (twistedAction transposition).toMonoidHom := by
  rw [← ofAut_twisted, lin_ofAut]

end
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization.BinaryMatrices

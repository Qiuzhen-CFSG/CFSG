module

public import Theory.GroupTheory.PGroup.InvariantFiberAutomorphisms
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.Init

/-!
# Small even Ree two profile stabilizers, first batch

The tables below give proposed order-centralizer counts on binary vector spaces.
Their stabilizers have exponent dividing four, as certified by kernel reduction
on the possible images of a basis. Encoding vectors as four-bit integers lets
the certificate use table lookups and XOR; the decoding lemmas prove that these
operations agree with the vector-space operations. The model predicates separately require an
actual Frattini quotient with these counts. No external group computation is
used to prove a statement about the Ree groups.

Source: the root convention of Shinoda (1975), (2.3), pp. 81–82, used by
`Recognition.ReeTwo.SmallEvenCandidates`. The rank-four rows correspond to
candidate indices 0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17. In each row the
basis lifts are the following positions in that candidate's displayed generator
list, counting from one:
  [1, 2, 3, 6]
  [1, 2, 3, 5]
  [1, 2, 3, 4]
  [1, 2, 3, 4]
  [1, 2, 3, 6]
  [1, 2, 3, 4]
  [1, 2, 3, 4]
  [1, 2, 3, 4]
  [1, 2, 3, 6]
  [1, 2, 3, 4]
  [1, 2, 3, 5]
  [1, 2, 3, 5]
  [1, 2, 3, 7]
  [1, 2, 3, 7]
  [1, 2, 3, 6]
  [1, 2, 3, 5]
The rank-three row is candidate 4, with basis positions [1,2,3]. Cosets are
indexed by binary digits in this basis order, least significant first.
-/

namespace ReeTwo.SmallEvenAutProfilesA

/-- Rank-four row indices in the 59-candidate enumeration. -/
@[expose] public def fourIndex : Fin 16 → Fin 59 :=
  ![0, 1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

public abbrev FourQuotient := Multiplicative (Fin 4 → ZMod 2)
public abbrev ThreeQuotient := Multiplicative (Fin 3 → ZMod 2)

/-- The two intrinsic tests in each rank-four row. -/
@[expose] public def fourTests (i : Fin 16) : Fin 2 → ℕ × ℕ × ℕ :=
  (![![(4, 32, 0), (4, 64, 0)],
    ![(4, 32, 0), (4, 64, 0)],
    ![(2, 128, 0), (4, 32, 0)],
    ![(4, 32, 0), (4, 128, 0)],
    ![(4, 32, 0), (4, 64, 0)],
    ![(2, 64, 0), (4, 32, 0)],
    ![(2, 128, 0), (4, 32, 0)],
    ![(2, 256, 0), (4, 32, 0)],
    ![(2, 256, 0), (4, 32, 0)],
    ![(2, 256, 0), (4, 64, 0)],
    ![(2, 128, 0), (4, 64, 0)],
    ![(2, 64, 0), (4, 128, 0)],
    ![(2, 256, 0), (4, 64, 0)],
    ![(2, 128, 0), (4, 32, 0)],
    ![(2, 128, 0), (4, 64, 0)],
    ![(2, 256, 0), (4, 64, 0)]]) i

/-- Proposed rank-four counts, indexed by binary masks. -/
@[expose] public def fourTable (i : Fin 16) : List (ℕ × ℕ) :=
  (![([(0, 0), (0, 0), (0, 0), (0, 32), (16, 0), (16, 0), (0, 32), (16, 16), (0, 16), (0, 0), (0, 0), (32, 0), (32, 0), (16, 0), (0, 32), (32, 0)] : List (ℕ × ℕ)),
    ([(0, 16), (0, 0), (0, 0), (0, 32), (16, 0), (16, 0), (32, 0), (16, 16), (0, 16), (0, 0), (0, 0), (16, 0), (16, 16), (16, 0), (32, 0), (16, 16)] : List (ℕ × ℕ)),
    ([(8, 0), (0, 16), (0, 0), (0, 32), (0, 16), (0, 32), (0, 0), (0, 32), (16, 0), (0, 16), (0, 0), (0, 16), (0, 16), (0, 32), (0, 0), (0, 16)] : List (ℕ × ℕ)),
    ([(0, 16), (0, 16), (0, 0), (0, 0), (32, 0), (16, 0), (0, 0), (0, 0), (32, 0), (16, 0), (0, 0), (0, 0), (0, 0), (0, 16), (0, 0), (0, 0)] : List (ℕ × ℕ)),
    ([(0, 0), (0, 0), (16, 0), (16, 16), (0, 32), (0, 32), (0, 0), (0, 0), (0, 8), (0, 16), (32, 0), (32, 0), (0, 32), (0, 32), (0, 0), (0, 0)] : List (ℕ × ℕ)),
    ([(0, 0), (0, 8), (0, 0), (0, 16), (8, 8), (0, 8), (0, 0), (0, 0), (4, 0), (0, 8), (0, 0), (0, 16), (8, 8), (0, 8), (0, 0), (0, 0)] : List (ℕ × ℕ)),
    ([(12, 0), (0, 8), (0, 0), (0, 16), (16, 0), (0, 8), (0, 0), (0, 16), (0, 0), (0, 8), (0, 0), (0, 16), (0, 0), (0, 8), (0, 0), (0, 16)] : List (ℕ × ℕ)),
    ([(3, 0), (0, 8), (0, 16), (0, 0), (4, 0), (0, 8), (0, 16), (0, 0), (0, 16), (0, 8), (0, 16), (0, 16), (0, 16), (0, 8), (0, 16), (0, 16)] : List (ℕ × ℕ)),
    ([(3, 0), (0, 8), (0, 16), (0, 16), (0, 8), (0, 16), (0, 16), (0, 0), (4, 0), (0, 8), (0, 16), (0, 16), (0, 8), (0, 16), (0, 16), (0, 0)] : List (ℕ × ℕ)),
    ([(1, 0), (0, 0), (0, 0), (0, 16), (0, 8), (0, 0), (0, 0), (0, 16), (2, 0), (0, 0), (0, 0), (0, 16), (0, 8), (0, 0), (0, 0), (0, 16)] : List (ℕ × ℕ)),
    ([(12, 0), (0, 0), (0, 16), (0, 16), (0, 8), (0, 16), (0, 16), (0, 16), (16, 0), (0, 0), (0, 16), (0, 16), (0, 8), (0, 16), (0, 16), (0, 16)] : List (ℕ × ℕ)),
    ([(0, 8), (0, 16), (0, 0), (0, 0), (16, 0), (0, 0), (0, 0), (0, 0), (8, 0), (0, 0), (0, 0), (0, 0), (16, 0), (0, 0), (0, 0), (0, 0)] : List (ℕ × ℕ)),
    ([(1, 0), (0, 0), (0, 16), (0, 0), (0, 0), (0, 8), (0, 0), (0, 16), (2, 0), (0, 0), (0, 16), (0, 0), (0, 0), (0, 8), (0, 0), (0, 16)] : List (ℕ × ℕ)),
    ([(12, 0), (0, 8), (0, 0), (0, 16), (0, 8), (0, 0), (0, 16), (0, 0), (16, 0), (0, 8), (0, 0), (0, 16), (0, 8), (0, 0), (0, 16), (0, 0)] : List (ℕ × ℕ)),
    ([(12, 0), (0, 8), (0, 16), (0, 16), (0, 16), (0, 16), (0, 0), (0, 16), (16, 0), (0, 8), (0, 16), (0, 16), (0, 16), (0, 16), (0, 0), (0, 16)] : List (ℕ × ℕ)),
    ([(1, 0), (0, 8), (0, 0), (0, 0), (0, 0), (0, 0), (0, 16), (0, 16), (2, 0), (0, 8), (0, 0), (0, 0), (0, 0), (0, 0), (0, 16), (0, 16)] : List (ℕ × ℕ))]) i

/-- Proposed counts in the sixteen binary cosets. -/
@[expose] public def fourProfile (i : Fin 16) (x : FourQuotient) : ℕ × ℕ :=
  (fourTable i).getD
    ((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val +
      8 * (x.toAdd 3).val) (0, 0)

/-- The intrinsic test for the rank-three row. -/
@[expose] public def threeTest : ℕ × ℕ × ℕ := (4, 32, 0)

/-- Proposed counts in the eight binary cosets. -/
@[expose] public def threeProfile (x : ThreeQuotient) : ℕ :=
  ([16, 48, 0, 0, 32, 48, 0, 0] : List ℕ).getD
    ((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val) 0

private def basisVector (n : ℕ) (i : Fin n) : Multiplicative (Fin n → ZMod 2) :=
  Multiplicative.ofAdd (fun j => if j = i then 1 else 0)

private def word4 (a b c d : FourQuotient) (x : FourQuotient) : FourQuotient :=
  a ^ (x.toAdd 0).val * b ^ (x.toAdd 1).val * c ^ (x.toAdd 2).val * d ^ (x.toAdd 3).val

private def word3 (a b c : ThreeQuotient) (x : ThreeQuotient) : ThreeQuotient :=
  a ^ (x.toAdd 0).val * b ^ (x.toAdd 1).val * c ^ (x.toAdd 2).val

set_option synthInstance.maxSize 4096
set_option maxRecDepth 16384
private def decode4 (x : Fin 16) : FourQuotient :=
  Multiplicative.ofAdd ![(x.val : ZMod 2), ((x.val / 2 : ℕ) : ZMod 2),
    ((x.val / 4 : ℕ) : ZMod 2), ((x.val / 8 : ℕ) : ZMod 2)]

private def encode4 (x : FourQuotient) : Fin 16 :=
  ⟨((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val +
    8 * (x.toAdd 3).val) % 16, Nat.mod_lt _ (by decide)⟩

private theorem decode4_encode4 : ∀ x, decode4 (encode4 x) = x := by decide +kernel

private theorem decode4_xor : ∀ a b, decode4 (a ^^^ b) = decode4 a * decode4 b := by
  decide +kernel

private def color4 (i : Fin 16) (x : Fin 16) : ℕ × ℕ :=
  (fourTable i).getD x.val (0, 0)

private theorem color4_decode : ∀ i x, fourProfile i (decode4 x) = color4 i x := by
  decide +kernel

@[simp] private theorem bits_zero_xor (a : Fin 16) : (0 : Fin 16) ^^^ a = a := by
  rw [Fin.xor_comm, Fin.xor_zero]

private def wordBits (a b c d x : Fin 16) : Fin 16 :=
  (if x.val % 2 = 0 then 0 else a) ^^^
    (if x.val / 2 % 2 = 0 then 0 else b) ^^^
    (if x.val / 4 % 2 = 0 then 0 else c) ^^^
    (if x.val / 8 % 2 = 0 then 0 else d)

private theorem decode4_zero : decode4 0 = 1 := by decide +kernel

private theorem decode4_digits : ∀ x : Fin 16,
    (decode4 x |>.toAdd 0).val = x.val % 2 ∧
    (decode4 x |>.toAdd 1).val = x.val / 2 % 2 ∧
    (decode4 x |>.toAdd 2).val = x.val / 4 % 2 ∧
    (decode4 x |>.toAdd 3).val = x.val / 8 % 2 := by decide +kernel

private theorem decode4_wordBits (a b c d x : Fin 16) :
    decode4 (wordBits a b c d x) =
      word4 (decode4 a) (decode4 b) (decode4 c) (decode4 d) (decode4 x) := by
  unfold wordBits
  simp only [decode4_xor]
  unfold word4
  rw [(decode4_digits x).1, (decode4_digits x).2.1,
    (decode4_digits x).2.2.1, (decode4_digits x).2.2.2]
  fin_cases x <;> norm_num [decode4_zero]

set_option maxHeartbeats 16000000 in
private theorem certificate4 : ∀ i : Fin 16,
    ∀ a : Fin 16, color4 i a = color4 i 1 →
    ∀ b : Fin 16, color4 i b = color4 i 2 →
    color4 i (a ^^^ b) = color4 i 3 →
    ∀ c : Fin 16, color4 i c = color4 i 4 →
    color4 i (a ^^^ c) = color4 i 5 →
    color4 i (b ^^^ c) = color4 i 6 →
    color4 i (a ^^^ b ^^^ c) = color4 i 7 →
    ∀ d : Fin 16, color4 i d = color4 i 8 →
    (∀ x, color4 i (wordBits a b c d x) = color4 i x) →
    ∀ x, wordBits a b c d (wordBits a b c d (wordBits a b c d (wordBits a b c d x))) = x := by
  decide +kernel

private theorem word4_hom (f : FourQuotient →* FourQuotient) (x : FourQuotient) :
    word4 (f (basisVector 4 0)) (f (basisVector 4 1))
      (f (basisVector 4 2)) (f (basisVector 4 3)) x = f x := by
  have hn : word4 (basisVector 4 0) (basisVector 4 1)
      (basisVector 4 2) (basisVector 4 3) x = x :=
    (by decide +kernel : ∀ x, word4 (basisVector 4 0) (basisVector 4 1)
      (basisVector 4 2) (basisVector 4 3) x = x) x
  simpa only [word4, map_mul, map_pow] using congrArg f hn

/-- Every symmetry of a rank-four profile has fourth power one. -/
public theorem fourProfile_aut_fourth (i : Fin 16) (f : MulAut FourQuotient)
    (h : ∀ x, fourProfile i (f x) = fourProfile i x) : f ^ 4 = 1 := by
  let a := encode4 (f (basisVector 4 0))
  let b := encode4 (f (basisVector 4 1))
  let c := encode4 (f (basisVector 4 2))
  let d := encode4 (f (basisVector 4 3))
  have hw (x : Fin 16) : decode4 (wordBits a b c d x) = f (decode4 x) := by
    rw [decode4_wordBits]
    simp only [a, b, c, d, decode4_encode4]
    exact word4_hom f.toMonoidHom (decode4 x)
  have hp (x : Fin 16) : color4 i (wordBits a b c d x) = color4 i x := by
    rw [← color4_decode, ← color4_decode, hw]
    exact h _
  have hc := certificate4 i a (by simpa [wordBits] using hp 1)
    b (by simpa [wordBits] using hp 2) (by simpa [wordBits] using hp 3)
    c (by simpa [wordBits] using hp 4) (by simpa [wordBits] using hp 5)
    (by simpa [wordBits] using hp 6) (by simpa [wordBits] using hp 7)
    d (by simpa [wordBits] using hp 8) hp
  apply MulEquiv.ext
  intro x
  change f (f (f (f x))) = x
  simpa only [hw, decode4_encode4] using congrArg decode4 (hc (encode4 x))

set_option maxHeartbeats 1000000 in
private theorem certificate3 :
    ∀ a : ThreeQuotient, threeProfile a = threeProfile (basisVector 3 0) →
    ∀ b : ThreeQuotient, threeProfile b = threeProfile (basisVector 3 1) →
    ∀ c : ThreeQuotient, threeProfile c = threeProfile (basisVector 3 2) →
    (∀ x, threeProfile (word3 a b c x) = threeProfile x) →
    ∀ x, word3 a b c (word3 a b c (word3 a b c (word3 a b c x))) = x := by
  decide +kernel

private theorem word3_hom (f : ThreeQuotient →* ThreeQuotient) (x : ThreeQuotient) :
    word3 (f (basisVector 3 0)) (f (basisVector 3 1)) (f (basisVector 3 2)) x = f x := by
  have hn : word3 (basisVector 3 0) (basisVector 3 1) (basisVector 3 2) x = x :=
    (by decide +kernel : ∀ x, word3 (basisVector 3 0) (basisVector 3 1)
      (basisVector 3 2) x = x) x
  simpa only [word3, map_mul, map_pow] using congrArg f hn

/-- Every symmetry of the rank-three profile has fourth power one. -/
public theorem threeProfile_aut_fourth (f : MulAut ThreeQuotient)
    (h : ∀ x, threeProfile (f x) = threeProfile x) : f ^ 4 = 1 := by
  have hc := certificate3 (f (basisVector 3 0)) (h _) (f (basisVector 3 1)) (h _)
    (f (basisVector 3 2)) (h _)
  have hw := word3_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  apply MulEquiv.ext
  intro x
  change f (f (f (f x))) = x
  simpa only [hw] using hh x

/-- Realization of a rank-four profile by a group's actual Frattini quotient. -/
@[expose] public def FourModel (G : Type*) [Group G] (i : Fin 16) : Prop :=
  ∃ π : G →* FourQuotient,
    Function.Surjective π ∧ π.ker = frattini G ∧
    ∀ v, (π.predicateFiberCard (MulAut.orderCentralizerTest (fourTests i 0)) v,
      π.predicateFiberCard (MulAut.orderCentralizerTest (fourTests i 1)) v) =
      fourProfile i v

/-- Realization of the rank-three profile by a group's actual Frattini quotient. -/
@[expose] public def ThreeModel (G : Type*) [Group G] : Prop :=
  ∃ π : G →* ThreeQuotient,
    Function.Surjective π ∧ π.ker = frattini G ∧
    ∀ v, π.predicateFiberCard (MulAut.orderCentralizerTest threeTest) v = threeProfile v

/-- A realized rank-four profile excludes odd-order automorphisms. -/
public theorem isPGroup_mulAut_of_fourModel {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (i : Fin 16) (h : FourModel G i) : IsPGroup 2 (MulAut G) := by
  obtain ⟨π, hπ, hker, hcount⟩ := h
  apply MonoidHom.isPGroup_mulAut_of_frattini_predicateFiber hG π hπ hker
    (fun j : Fin 2 => MulAut.orderCentralizerTest (fourTests i j))
    (fun f j x => MulAut.orderCentralizerTest_apply f _ x)
  intro a ha
  refine ⟨2, fourProfile_aut_fourth i a ?_⟩
  intro v
  rw [← hcount (a v), ← hcount v, ha 0 v, ha 1 v]

/-- A realized rank-three profile excludes odd-order automorphisms. -/
public theorem isPGroup_mulAut_of_threeModel {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (h : ThreeModel G) : IsPGroup 2 (MulAut G) := by
  obtain ⟨π, hπ, hker, hcount⟩ := h
  apply MonoidHom.isPGroup_mulAut_of_frattini_predicateFiber hG π hπ hker
    (fun _ : Unit => MulAut.orderCentralizerTest threeTest)
    (fun f _ x => MulAut.orderCentralizerTest_apply f _ x)
  intro a ha
  refine ⟨2, threeProfile_aut_fourth a ?_⟩
  intro v
  rw [← hcount (a v), ← hcount v, ha () v]

end ReeTwo.SmallEvenAutProfilesA

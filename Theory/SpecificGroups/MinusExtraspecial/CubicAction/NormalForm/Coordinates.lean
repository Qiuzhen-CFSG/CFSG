module

public import Theory.SpecificGroups.MinusExtraspecial.CubicAction
public import Mathlib.Data.BitVec

/-!
# Five-bit coordinates for cubic automorphism certificates

The low three bits encode a quaternion and the last two bits encode the
reflection coordinates. Multiplication, inversion, generator words, and the
standard cubic action are identified with the literal operations on `Model`.
Every automorphism supplies a tuple satisfying the displayed presentation
relations. Cubicity and nontriviality are detected on the four generators.

To verify a candidate multiplicative equivalence it suffices to check right
multiplication by these generators: `multiplicative_of_generators` extends
those identities through every canonical coordinate word. Thus a certificate
uses 128 multiplication checks instead of all 1024 pairs. Explicit tables
avoid repeatedly evaluating the conjugator words within these checks.

The bit arithmetic follows `MinusExtraspecial/ModelFixedFourCalculation.lean`;
it is repeated here to avoid importing that unrelated square-action certificate.
Source: Aschbacher, *Sporadic Groups* (1994), 47.5, p.263, and p.265.
-/

@[expose] public section
namespace MinusExtraspecial.CubicAction.NormalForm
abbrev B := BitVec 5
instance : Fintype B := Fintype.ofEquiv (Fin 32) (BitVec.equivFin (m := 5)).toEquiv.symm
/-- Four generator images, in the order quaternion i, quaternion j, r, s. -/
structure Images where
  u : B
  v : B
  r : B
  s : B
  deriving DecidableEq

def mul (a b : B) : B :=
  let low := a ^^^ b
  let carry := ((a &&& b) <<< 1) &&& 2
  let neg := ((b >>> 2) &&& a) <<< 1 &&& 2
  let quat := ((a &&& b) >>> 1) &&& 2
  let twist := ((a >>> 3) &&& (b >>> 2)) &&& 2
  low ^^^ carry ^^^ neg ^^^ quat ^^^ twist
def inv (a : B) : B := a ^^^ mul a a
def word (a : Images) (x : B) : B :=
  mul (mul (mul (mul (if x[2] then a.v else 0)
    (if x[1] then mul a.u a.u else 0)) (if x[0] then a.u else 0))
    (if x[3] then a.r else 0)) (if x[4] then a.s else 0)
def sigma (x : B) : B :=
  (x &&& 24) ||| (match (x &&& 7).toNat with
    | 0 => 0 | 1 => 5 | 2 => 2 | 3 => 7 | 4 => 3 | 5 => 6 | 6 => 1 | _ => 4)
def gens : List B := [1,4,8,16]
def all : List B := List.range 32 |>.map (BitVec.ofNat 5)
/-- A coordinate table evaluated on the five-bit input. Missing entries default
to zero; the checked inverse identities in `rowCheck` rule out malformed tables. -/
def table (t : Array B) (x : B) : B := t[x.toNat]?.getD 0

/-- A candidate action and explicit tables for its conjugator and inverse. -/
structure Row where
  a : Images
  e : Array B
  d : Array B
  deriving DecidableEq

/-- Multiplication by generators, both inverse identities, and exact conjugacy. -/
def rowCheck (t : Row) : Bool :=
  (all.all fun x => gens.all fun y =>
    table t.e (mul x y) == mul (table t.e x) (table t.e y)) &&
  (all.all fun x => table t.d (table t.e x) == x) &&
  (all.all fun x => table t.e (table t.d x) == x) &&
  (all.all fun x => table t.e (word t.a x) == sigma (table t.e x))

def decode (x : B) : Model :=
  ⟨if x[2] then .xa ((x.toNat % 4 : ℕ) : ZMod 4) else .a ((x.toNat % 4 : ℕ) : ZMod 4), x[3], x[4]⟩
def encode (x : Model) : B :=
  (match x.q with | .a i => BitVec.ofNat 5 i.val | .xa i => BitVec.ofNat 5 (i.val + 4)) +
    (if x.r then 8 else 0) + (if x.s then 16 else 0)
theorem decode_encode : ∀ x, decode (encode x) = x := by decide +kernel
theorem encode_decode : ∀ x, encode (decode x) = x := by decide +kernel
theorem decode_mul : ∀ x y, decode (mul x y) = decode x * decode y := by decide +kernel
theorem decode_inv : ∀ x, decode (inv x) = (decode x)⁻¹ := by decide +kernel
theorem decode_zero : decode 0 = 1 := rfl
def equiv : B ≃ Model := ⟨decode, encode, encode_decode, decode_encode⟩
theorem decode_sigma : ∀ x : B, decode (sigma x) = cycle (decode x) := by decide +kernel

theorem decomposition : ∀ x : B, decode x =
    (if x[2] then generators 1 else 1) *
    (if x[1] then generators 0 * generators 0 else 1) *
    (if x[0] then generators 0 else 1) *
    (if x[3] then generators 2 else 1) *
    (if x[4] then generators 3 else 1) := by decide +kernel

def images (a : MulAut Model) : Images :=
  ⟨encode (a (generators 0)), encode (a (generators 1)),
   encode (a (generators 2)), encode (a (generators 3))⟩
theorem decode_word (a : MulAut Model) (x : B) :
    decode (word (images a) x) = a (decode x) := by
  conv_rhs => rw [decomposition x]
  simp only [word, images, decode_mul, apply_ite decode, decode_encode, decode_zero,
    map_mul, apply_ite a, map_one]

theorem multiplicative_of_generators (f : Model → Model)
    (h : ∀ x i, f (x * generators i) = f x * f (generators i)) :
    ∀ x y, f (x * y) = f x * f y := by
  have hone : f 1 = 1 := by
    have h1 := h 1 0
    rw [one_mul] at h1
    exact mul_right_cancel (h1.symm.trans (one_mul _).symm)
  let Good (y : Model) : Prop := ∀ x, f (x * y) = f x * f y
  have h_one : Good 1 := by intro x; simp [hone]
  have h_gen (i : Fin 4) : Good (generators i) := fun x => h x i
  have h_mul (y z : Model) (hy : Good y) (hz : Good z) : Good (y * z) := by
    intro x
    rw [← mul_assoc, hz, hy, mul_assoc, hz]
  have h_pow (i : Fin 4) (n : ℕ) : Good (generators i ^ n) := by
    induction n with
    | zero => simpa only [pow_zero] using h_one
    | succ n ih => simpa only [pow_succ] using h_mul _ _ ih (h_gen i)
  intro x y
  have hw : Good (MinusExtraspecial.word generators y) := by
    unfold MinusExtraspecial.word
    apply h_mul
    · apply h_mul
      · cases y.q with
        | a i => exact h_pow 0 i.val
        | xa i => exact h_mul _ _ (h_gen 1) (h_pow 0 i.val)
      · split
        · exact h_gen 2
        · exact h_one
    · split
      · exact h_gen 3
      · exact h_one
  simpa only [word_generators] using hw x

theorem mem_all : ∀ x : B, x ∈ all := by decide +kernel
theorem gens_mem : ∀ i : Fin 4, encode (generators i) ∈ gens := by decide +kernel

def relations (a : Images) : Bool :=
  mul a.u a.u != 0 && mul a.v a.v == mul a.u a.u &&
  mul a.v a.u == mul (inv a.u) a.v &&
  mul a.r a.r == 0 && mul a.r a.u == mul a.u a.r && mul a.r a.v == mul a.v a.r &&
  mul a.s a.s == 0 && mul a.s a.u == mul a.u a.s && mul a.s a.v == mul a.v a.s &&
  mul a.s a.r == mul (mul (mul a.u a.u) a.r) a.s

def cubic (a : Images) : Bool :=
  gens.all fun g => word a (word a (word a g)) == g

def nontrivial (a : Images) : Bool :=
  gens.any fun g => word a g != g

theorem relations_aut (a : MulAut Model) : relations (images a) := by
  simp only [relations, images, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
    ne_eq, ← equiv.injective.eq_iff]
  dsimp only [equiv]
  simp only [Equiv.coe_fn_mk, decode_mul, decode_inv, decode_encode, decode_zero,
    ← map_mul, ← map_inv, a.injective.eq_iff, a.map_eq_one_iff]
  decide

theorem cubic_aut (a : MulAut Model) (ha : a ^ 3 = 1) : cubic (images a) := by
  apply List.all_eq_true.mpr
  intro g _
  apply beq_iff_eq.mpr
  apply equiv.injective
  change decode (word (images a) (word (images a) (word (images a) g))) = decode g
  rw [decode_word, decode_word, decode_word]
  have h := congrArg (fun c : MulAut Model => c (decode g)) ha
  simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using h

theorem nontrivial_aut (a : MulAut Model) (ha : a ≠ 1) : nontrivial (images a) := by
  by_contra hn
  have hz := List.any_eq_false.mp (Bool.eq_false_iff.mpr hn)
  have hf (i : Fin 4) : a (generators i) = generators i := by
    have hi := hz (encode (generators i)) (gens_mem i)
    have hi' : word (images a) (encode (generators i)) = encode (generators i) := by
      simpa only [bne_iff_ne, not_not] using hi
    have hd := congrArg decode hi'
    simpa only [decode_word, decode_encode] using hd
  apply ha
  apply DFunLike.ext
  intro x
  change a x = x
  rw [← aut_word a x]
  simpa only [hf] using word_generators x

end MinusExtraspecial.CubicAction.NormalForm

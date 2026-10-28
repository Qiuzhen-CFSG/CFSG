module

public import Theory.Representation.BinaryCubicPairs.Packed

/-!
# Word certificates for pairs of binary cubic actors

A certificate gives a nonidentity involution word and two vectors bounding
its displacement in every extension with trivial quotient. The coefficients
of a word's displacement are computed by the cocycle identity. Their equality
with the stored matrices is checked once, rather than expanding the word for
every vector. All certificate fields are verified by the Boolean checker.

This is the finite arithmetic interface for the four-dimensional pair
reduction in Aschbacher--Smith E.6.24, printed p.255.
-/

@[expose] public section
namespace BinaryCubicPairs
namespace Packed

def ident : BitVec 16 := 0x8421

def cubic : BitVec 16 := 0x8432

def word (d : BitVec 16) : List Bool → BitVec 16
  | [] => ident
  | b :: w => mm (if b then d else cubic) (word d w)

def coefficients (d : BitVec 16) : List Bool → BitVec 16 × BitVec 16
  | [] => (0, 0)
  | b :: w =>
    let r := coefficients d w
    if b then (mm d r.1, ident ^^^ mm d r.2)
    else (ident ^^^ mm cubic r.1, mm cubic r.2)

structure Certificate where
  sequence : List Bool
  actor : BitVec 16
  leftCoefficient : BitVec 16
  rightCoefficient : BitVec 16
  first : BitVec 4
  second : BitVec 4

def readyB (d : BitVec 16) : Bool :=
  mm (mm d d) d == ident &&
    ((List.range 16).countP (fun z => mv d (BitVec.ofNat 4 z) == BitVec.ofNat 4 z) == 4) &&
    ((List.range 4).all fun q => (List.range 16).any fun z =>
      (mv d (BitVec.ofNat 4 z) ^^^ BitVec.ofNat 4 z).extractLsb' 2 2 == BitVec.ofNat 2 q) &&
    !(mm cubic d == mm d cubic)

def validB (d : BitVec 16) (k : Certificate) : Bool :=
  (word d k.sequence == k.actor) &&
    (coefficients d k.sequence == (k.leftCoefficient, k.rightCoefficient)) &&
    (!(k.actor == ident)) && (mm k.actor k.actor == ident) &&
    ((List.range 4).all fun x => (List.range 16).all fun z =>
      let y := mv d (BitVec.ofNat 4 z) ^^^ BitVec.ofNat 4 z
      let u := mv k.leftCoefficient (BitVec.ofNat 4 x) ^^^ mv k.rightCoefficient y
      (!(mv k.actor u == u)) || u == 0 || u == k.first || u == k.second || u == k.first ^^^ k.second)

/-- The exact mathematical content of a checked word certificate. -/
structure Valid (d : BitVec 16) (k : Certificate) : Prop where
  word_eq : word d k.sequence = k.actor
  coefficients_eq : coefficients d k.sequence = (k.leftCoefficient, k.rightCoefficient)
  nontrivial : k.actor ≠ ident
  square : mm k.actor k.actor = ident
  displacement : ∀ x : Fin 4, ∀ z : BitVec 4,
    let y := mv d z ^^^ z
    let u := mv k.leftCoefficient (BitVec.ofNat 4 x) ^^^ mv k.rightCoefficient y
    mv k.actor u = u →
      u = 0 ∨ u = k.first ∨ u = k.second ∨ u = k.first ^^^ k.second

/-- Boolean reflection does not trust the generated words or coefficients. -/
theorem valid_of_check {d : BitVec 16} {k : Certificate} (h : validB d k = true) :
    Valid d k := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.eq_false_iff] at h
  refine ⟨h.1.1.1.1, h.1.1.1.2, (fun he => h.1.1.2 (beq_iff_eq.mpr he)), h.1.2, ?_⟩
  intro x z
  have hx := List.all_eq_true.mp h.2 x.val (List.mem_range.mpr x.isLt)
  have hz := List.all_eq_true.mp hx z.toNat (List.mem_range.mpr z.isLt)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true', Bool.eq_false_iff] at hz
  dsimp only
  intro he
  rcases hz with (((hn | hu) | hu) | hu) | hu
  · exact (hn (beq_iff_eq.mpr he)).elim
  · exact Or.inl hu
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr (Or.inl hu))
  · exact Or.inr (Or.inr (Or.inr hu))

end Packed
end BinaryCubicPairs

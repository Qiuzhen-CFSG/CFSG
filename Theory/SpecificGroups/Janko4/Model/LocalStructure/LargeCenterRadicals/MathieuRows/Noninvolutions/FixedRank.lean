module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.NormalWeights.Core
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.FastAction
/-!
# Small checked certificates for fixed-space rank

A fixed mask is determined by its selected coordinates if the only fixed
mask vanishing on those coordinates is zero. XOR-linearity proves injectivity
of the coordinate restriction. A four-coordinate image then has at most
sixteen elements. The finite tests evaluate the eleven-row action only on
masks whose selected coordinates vanish, avoiding a repeated full count.

The row action and XOR-linearity are the native ATLAS max1 coordinate action
of `ElementaryBound.FastAction`; no numerical rank computation is trusted.
-/
@[expose] public section
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions
open Cardinality.QuotientCount.Image SylowCore.FiniteBoundCertificate.NormalWeights
open ElementaryNormalizerCover.ElementaryBound

def CoordinateMasks (f : ℕ) := {m : Fin 2048 // m.val &&& f = m.val}
instance (f : ℕ) : Fintype (CoordinateMasks f) := inferInstanceAs (Fintype {_m : Fin 2048 // _})

def ZeroFixedTest (r : Fin 11 → ℕ) (f : ℕ) : Bool :=
  (List.finRange 2048).all (fun m =>
    if m.val &&& f == 0 then (maskImage r m.val != m.val) || (m.val == 0) else true)

theorem fixed_bound_of_coordinates (r : Fin 11 → ℕ) (f : ℕ)
    (hz : ZeroFixedTest r f = true) (hc : Fintype.card (CoordinateMasks f) ≤ 16) :
    Nat.card {m : Fin 2048 // maskImage r m.val = m.val} ≤ 16 := by
  have hzero (m : Fin 2048) (hf : m.val &&& f = 0) (hm : maskImage r m.val = m.val) : m.val = 0 := by
    have hh := List.all_eq_true.mp hz m (List.mem_finRange _)
    simpa only [hf, beq_self_eq_true, ↓reduceIte, hm, bne_self_eq_false, Bool.false_or, beq_iff_eq] using hh
  let j : {m : Fin 2048 // maskImage r m.val = m.val} → CoordinateMasks f := fun m =>
    ⟨⟨m.val.val &&& f, lt_of_le_of_lt Nat.and_le_left m.val.isLt⟩, by
      simp only [Nat.and_assoc, Nat.and_self]⟩
  have hj : Function.Injective j := by
    intro a b h
    have he : a.val.val &&& f = b.val.val &&& f := congrArg (fun m : CoordinateMasks f => m.val.val) h
    have hx : a.val.val ^^^ b.val.val = 0 := hzero
      ⟨a.val.val ^^^ b.val.val, Nat.xor_lt_two_pow (n := 11) a.val.isLt b.val.isLt⟩
      (by rw [Nat.and_xor_distrib_right, he, Nat.xor_self])
      (by rw [maskImage_xor,a.property,b.property])
    exact Subtype.ext (Fin.ext (Nat.xor_eq_zero_iff.mp hx))
  exact (Nat.card_le_card_of_injective j hj).trans (by simpa only [Nat.card_eq_fintype_card] using hc)
end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions

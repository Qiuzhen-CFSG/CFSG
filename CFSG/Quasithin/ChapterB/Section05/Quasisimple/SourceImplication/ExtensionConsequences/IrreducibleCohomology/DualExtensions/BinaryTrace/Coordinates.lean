module

public import Theory.AtlasPort.LinearGroups.G2.Unipotent
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Fintype.Card

/-!
# The small coordinate certificate for binary octonion trace detection

The positive-root subgroup of the full octonion automorphism group has six
binary coordinates. For a trace-one octonion, its coordinates 0 and 4 may be
removed by adding fixed vectors. The remaining five coordinates define `normal`.
Outside the four-element plane A B, each involution fixing this vector modulo
the scalar line commutes with at most four such involutions. The certificate
checks only the 64 positive-root parameter tuples, using the actual eight
coordinate action. Four separate kernel checks bound peak reduction memory.

The scalar-fixation predicate retains only five necessary coordinate equations;
this enlarges the set being counted, so the resulting upper bound is sufficient.
Its application to actual scalar displacements is proved in `SylowGeometry`.

Source: Aschbacher–Smith, B.5.1(5), I.1.7(b), and B.4.6(3),(13), printed
pp.102–103, 408–409, 88–90. The root coordinates and product law are the
licensed ATLAS ports imported above; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions.BinaryTrace
abbrev Params := Fin 6 → ZMod 2
abbrev Point := Fin 5 → ZMod 2

def normal (x : Point) : Carrier (ZMod 2) := ![0,x 0,x 1,1,0,x 2,x 3,x 4]

def shortProduct (t u : Params) : Params :=
  ![u 0 + u 1 * t 4 + u 2 * t 3 + u 2 * t 4 * t 5 + u 3 * t 5 +
      u 3 * u 4 * t 5 + u 3 * t 4 * t 5 + u 4 * t 5 +
      u 4 * t 3 * t 5 + u 4 * t 4 * t 5 + t 0,
    u 1 + u 2 * t 5 + u 3 * t 5 + u 4 * t 5 + t 1,
    u 2 + u 4 * t 5 + t 2, u 3 + u 4 * t 5 + t 3, u 4 + t 4, u 5 + t 5]

def fixes (x : Point) (t : Params) : Prop :=
  let y := (unipotentProduct t).val (normal x)
  y 0 = 0 ∧ y 1 = x 0 ∧ y 2 = x 1 ∧ y 5 = x 2 ∧ y 6 = x 3

instance (x : Point) (t : Params) : Decidable (fixes x t) := inferInstanceAs (Decidable (_ ∧ _))

def candidates (x : Point) (t : Params) : Finset Params :=
  Finset.univ.filter fun u => shortProduct u u = 0 ∧ fixes x u ∧ shortProduct t u = shortProduct u t

def plane (t : Params) : Prop := t 2 = 0 ∧ t 3 = 0 ∧ t 4 = 0 ∧ t 5 = 0
instance (t : Params) : Decidable (plane t) := inferInstanceAs (Decidable (_ ∧ _))
set_option maxRecDepth 10000 in
private theorem bound00 : ∀ z : Fin 3 → ZMod 2, ∀ t : Params, ¬ plane t →
    shortProduct t t = 0 → fixes ![z 0,z 1,z 2,0,0] t →
    (candidates ![z 0,z 1,z 2,0,0] t).card ≤ 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bound01 : ∀ z : Fin 3 → ZMod 2, ∀ t : Params, ¬ plane t →
    shortProduct t t = 0 → fixes ![z 0,z 1,z 2,0,1] t →
    (candidates ![z 0,z 1,z 2,0,1] t).card ≤ 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bound10 : ∀ z : Fin 3 → ZMod 2, ∀ t : Params, ¬ plane t →
    shortProduct t t = 0 → fixes ![z 0,z 1,z 2,1,0] t →
    (candidates ![z 0,z 1,z 2,1,0] t).card ≤ 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bound11 : ∀ z : Fin 3 → ZMod 2, ∀ t : Params, ¬ plane t →
    shortProduct t t = 0 → fixes ![z 0,z 1,z 2,1,1] t →
    (candidates ![z 0,z 1,z 2,1,1] t).card ≤ 4 := by
  decide +kernel

theorem shortProduct_eq (t u : Params) : shortProduct t u = unipotentProductParameters t u := by
  have hc (a : ZMod 2) : a ^ 3 = a := by rw [pow_succ, ZMod.pow_card, ← pow_two, ZMod.pow_card]
  ext i
  fin_cases i <;>
    simp [shortProduct, unipotentProductParameters, sub_eq_add_neg,
      ZMod.neg_eq_self_mod_two, ZMod.pow_card, hc, show (3 : ZMod 2) = 1 from rfl,
      show (6 : ZMod 2) = 0 from rfl, show (2 : ZMod 2) = 0 from rfl]

theorem bound (x : Point) (t : Params) (hn : ¬ plane t) (hs : shortProduct t t = 0)
    (hx : fixes x t) : (candidates x t).card ≤ 4 := by
  have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  have hrepr : x = ![x 0,x 1,x 2,x 3,x 4] := by ext i; fin_cases i <;> rfl
  rw [hrepr] at hx ⊢
  rcases hb (x 3) with h3 | h3 <;> rcases hb (x 4) with h4 | h4
  · simpa [h3, h4] using bound00 ![x 0,x 1,x 2] t hn hs (by simpa [h3,h4] using hx)
  · simpa [h3, h4] using bound01 ![x 0,x 1,x 2] t hn hs (by simpa [h3,h4] using hx)
  · simpa [h3, h4] using bound10 ![x 0,x 1,x 2] t hn hs (by simpa [h3,h4] using hx)
  · simpa [h3, h4] using bound11 ![x 0,x 1,x 2] t hn hs (by simpa [h3,h4] using hx)

def planeCodes : Finset Params := Finset.univ.filter plane

theorem planeCodes_card : planeCodes.card = 4 := by decide +kernel


end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions.BinaryTrace

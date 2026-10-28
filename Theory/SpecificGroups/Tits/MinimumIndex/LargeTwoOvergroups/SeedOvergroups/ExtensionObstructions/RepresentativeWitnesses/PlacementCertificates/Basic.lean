module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Cases
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.Membership
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Fast

/-!
# Rectangular certificates for literal placements

A rectangle is certified by an anchor u₀*r*v₀⁻¹ and the ratios u*u₀⁻¹,
v*v₀⁻¹ in the same actual place. Subgroup multiplication then certifies
u*r*v⁻¹ for every pair in the rectangle. Packed evaluation uses the already
proved inverse tables and `Geometry.Membership.placeTest_iff`.

Finite bit masks only encode unions of these rectangles. Their interpretation
below is proved for arbitrary lists, independently of the discovery data.
Source: Parrott (1972), §5, p.683, with the literal `placeWord` conjugators.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.Placement
open Geometry

namespace Fast
open Geometry.RepresentativeProducts

def test (g : Equiv.Perm (Fin 1600)) (j : Fin 38) : Bool :=
  let w := conjugator j
  let x := w⁻¹ * g * w
  if j.val < 17 then sameBase (x * centralPerm) (centralPerm * x)
  else centerImageTest x centralPerm && centerImageTest x matePerm

def trans (t : Fin 23) (a : Fin 32) := normalForm (transversalPattern t a)
def rep (k : Fin 18) := ((ConverseLocalCoverage.doubleCosetWord k).map assignment).prod

theorem test_iff (g : Atlas1600Group) (j : Fin 38) :
    test g.val j = true ↔ g ∈ place j := by
  have he : test g.val j = placeTest g.val j := by
    simp only [test, placeTest, conjugator_eq]
  rw [he, placeTest_iff]

theorem trans_eq (t : Fin 23) (a : Fin 32) :
    trans t a = (atlas1600SylowTwoNormalForm (transversalPattern t a)).val := by
  rw [trans, normalForm_eq, fastNormalForm_eq]

theorem rep_eq (k : Fin 18) : rep k = (ConverseLocalCoverage.doubleCosetRep k).val := by
  have hw (w : List ParrottGenerator) :
      (w.map assignment).prod = ((w.map atlas1600ParrottAssignment).prod).val := by
    induction w with
    | nil => rfl
    | cons s w ih =>
      change assignment s * (w.map assignment).prod =
        (atlas1600ParrottAssignment s).val * ((w.map atlas1600ParrottAssignment).prod).val
      rw [assignment_eq, fastAssignment_eq, ih]
  exact hw _

end Fast

def trans (t : Fin 23) (a : Fin 32) : Atlas1600Group :=
  atlas1600SylowTwoNormalForm (transversalPattern t a)

def rep (t : Fin 23) (a b : Fin 32) (c : Fin 15) : Atlas1600Group :=
  trans t a * ConverseLocalCoverage.doubleCosetRep ⟨c.val + 3, by omega⟩ * (trans t b)⁻¹

structure Tile where
  pattern : Fin 23
  placeId : Fin 38
  coset : Fin 15
  leftAnchor : Fin 32
  rightAnchor : Fin 32
  left : List (Fin 32)
  right : List (Fin 32)

def ratioTest (t : Fin 23) (j : Fin 38) (a a₀ : Fin 32) : Bool :=
  Fast.test (Fast.trans t a * (Fast.trans t a₀)⁻¹) j

def anchorTest (d : Tile) : Bool :=
  Fast.test (Fast.trans d.pattern d.leftAnchor * Fast.rep ⟨d.coset.val + 3, by omega⟩ *
    (Fast.trans d.pattern d.rightAnchor)⁻¹) d.placeId

def tileTest (d : Tile) : Bool :=
  (d.left.all (fun a => ratioTest d.pattern d.placeId a d.leftAnchor)) &&
  (d.right.all (fun b => ratioTest d.pattern d.placeId b d.rightAnchor)) && anchorTest d

private theorem val_mul (a b : Atlas1600Group) : (a * b).val = a.val * b.val := rfl
private theorem val_inv (a : Atlas1600Group) : a⁻¹.val = a.val⁻¹ := rfl

theorem ratioTest_sound (t : Fin 23) (j : Fin 38) (a a₀ : Fin 32)
    (h : ratioTest t j a a₀ = true) : trans t a * (trans t a₀)⁻¹ ∈ place j := by
  apply (Fast.test_iff _ _).mp
  simpa only [ratioTest, Fast.trans_eq, trans, val_mul, val_inv] using h

theorem anchorTest_sound (d : Tile) (h : anchorTest d = true) :
    rep d.pattern d.leftAnchor d.rightAnchor d.coset ∈ place d.placeId := by
  apply (Fast.test_iff _ _).mp
  simpa only [anchorTest, Fast.trans_eq, Fast.rep_eq, rep, trans, val_mul, val_inv] using h

/-- The group identity expands one anchor to its whole rectangle. -/
theorem tileTest_sound (d : Tile) (h : tileTest d = true)
    (a b : Fin 32) (ha : a ∈ d.left) (hb : b ∈ d.right) :
    rep d.pattern a b d.coset ∈ place d.placeId := by
  obtain ⟨⟨hl, hr⟩, hbase⟩ :=
    (show (d.left.all (fun a => ratioTest d.pattern d.placeId a d.leftAnchor) = true ∧
      d.right.all (fun b => ratioTest d.pattern d.placeId b d.rightAnchor) = true) ∧
      anchorTest d = true by simpa only [tileTest, Bool.and_eq_true] using h)
  have hu := ratioTest_sound _ _ _ _ (List.all_eq_true.mp hl a ha)
  have hv := ratioTest_sound _ _ _ _ (List.all_eq_true.mp hr b hb)
  have hx := anchorTest_sound d hbase
  have hm := (place d.placeId).mul_mem ((place d.placeId).mul_mem hu hx)
    ((place d.placeId).inv_mem hv)
  convert hm using 1
  dsimp only [rep]
  group

/-- Bitwise union has an existential interpretation at every position. -/
def maskUnion : List Nat → Nat
  | [] => 0
  | n :: ns => n ||| maskUnion ns

theorem maskUnion_bit (ns : List Nat) (p : Nat) :
    (maskUnion ns).testBit p = true ↔ ∃ n ∈ ns, n.testBit p = true := by
  induction ns with
  | nil => simp [maskUnion]
  | cons n ns ih => simp only [maskUnion, Nat.testBit_or, Bool.or_eq_true, ih,
      List.mem_cons, exists_eq_or_imp]

def tileMask (d : Tile) : Nat :=
  maskUnion (d.left.flatMap fun a => d.right.map fun b => 2 ^ candidateIndex a b d.coset)

private theorem candidateIndex_injective (a b a' b' : Fin 32) (c c' : Fin 15)
    (h : candidateIndex a b c = candidateIndex a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  dsimp only [candidateIndex] at h
  have ha := a.isLt
  have hb := b.isLt
  have ha' := a'.isLt
  have hb' := b'.isLt
  have h1 : a.val = a'.val := by omega
  have h2 : b.val = b'.val := by omega
  have h3 : c.val = c'.val := by omega
  exact ⟨Fin.ext h1, Fin.ext h2, Fin.ext h3⟩

theorem tileMask_sound (d : Tile) (a b : Fin 32) (c : Fin 15)
    (h : (tileMask d).testBit (candidateIndex a b c) = true) :
    a ∈ d.left ∧ b ∈ d.right ∧ c = d.coset := by
  obtain ⟨n, hn, hbit⟩ := (maskUnion_bit _ _).mp h
  obtain ⟨a', ha', hn⟩ := List.mem_flatMap.mp hn
  obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hn
  have he : candidateIndex a' b' d.coset = candidateIndex a b c := by
    simpa only [Nat.testBit_two_pow, decide_eq_true_eq] using hbit
  obtain ⟨rfl, rfl, rfl⟩ := candidateIndex_injective _ _ _ _ _ _ he
  exact ⟨ha', hb', rfl⟩

/-- Kernel-tested literal generators prove containment of their closure. -/
theorem seed_le_of_tests (i : Fin 122) (j : Fin 38)
    (h : ∀ n ∈ seedIndices i, Fast.test (Geometry.RepresentativeProducts.normalForm n) j = true) :
    seed i ≤ place j := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨n, hn, rfl⟩
  apply (Fast.test_iff _ _).mp
  simpa only [Geometry.RepresentativeProducts.normalForm_eq, fastNormalForm_eq] using h n hn

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.Placement

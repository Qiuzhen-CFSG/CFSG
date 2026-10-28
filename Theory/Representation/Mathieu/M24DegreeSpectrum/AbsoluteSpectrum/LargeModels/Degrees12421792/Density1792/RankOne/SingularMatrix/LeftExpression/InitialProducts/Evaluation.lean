module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Arithmetic

/-!
# Explicit recursors for the product checker

The equations below preserve the original arithmetic but avoid course-of-values
recursion during kernel reduction. These definitions are noncomputable only
because the executable code generator does not compile the explicit recursors.
Every certificate uses kernel reduction. See `source/README.md` for measurements.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts

noncomputable def rowRec (t : Tree) : Nat → Nat :=
  Tree.rec (fun b a => if a % 2 == 1 then b else 0)
    (fun k _ _ rl rr a => if a == 0 then 0 else rl (a % 2^k) + rr (a / 2^k)) t

theorem rowRec_eq (t : Tree) (a : Nat) : rowRec t a = row a t := by
  induction t generalizing a with
  | leaf b => rfl
  | node k l r ihl ihr =>
    change (if a == 0 then 0 else rowRec l (a % 2^k) + rowRec r (a / 2^k)) = _
    rw [row, ihl, ihr]

noncomputable def flattenRec (t : Tree) : List Nat :=
  Tree.rec (fun b => [b]) (fun _ _ _ l r => l ++ r) t

theorem flattenRec_eq (t : Tree) : flattenRec t = flatten t := by
  induction t with
  | leaf b => rfl
  | node k l r ihl ihr =>
    change flattenRec l ++ flattenRec r = flatten l ++ flatten r
    rw [ihl, ihr]

noncomputable def checkTree (t : Tree) : Nat × Bool :=
  Tree.rec (fun _ => (1, true))
    (fun k _ _ l r => (l.1 + r.1, (l.1 == k) && l.2 && r.2)) t

theorem checkTree_length (t : Tree) : (checkTree t).1 = (flatten t).length := by
  induction t with
  | leaf b => rfl
  | node k l r ihl ihr =>
    change (checkTree l).1 + (checkTree r).1 = (flatten l ++ flatten r).length
    rw [List.length_append, ihl, ihr]

theorem checkTree_valid (t : Tree) (h : (checkTree t).2 = true) : Valid t := by
  induction t with
  | leaf b => trivial
  | node k l r ihl ihr =>
    change (((checkTree l).1 == k) && (checkTree l).2 && (checkTree r).2) = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨(checkTree_length l).symm.trans h.1.1, ihl h.1.2, ihr h.2⟩

noncomputable def checkSumsRec (t : Tree) (as : List Nat) : List Nat → Bool :=
  List.rec (fun ss => match ss with | [] => true | _ => false)
    (fun a _ next ss => match ss with
      | [] => false
      | s :: ss => (rowRec t a == s) && next ss) as

theorem checkSumsRec_eq (t : Tree) (as ss : List Nat) :
    checkSumsRec t as ss = checkSums t as ss := by
  induction as generalizing ss with
  | nil => cases ss <;> rfl
  | cons a as ih =>
    cases ss with
    | nil => rfl
    | cons s ss =>
      change ((rowRec t a == s) && checkSumsRec t as ss) = _
      rw [rowRec_eq, ih]
      rfl

noncomputable def parityRec (k : Nat) : Nat → Nat → Bool :=
  Nat.rec (fun x y => x % 2 == y % 2)
    (fun k prev x y => prev x y && prev (x / 4096^(2^k)) (y / 2^(2^k))) k

theorem parityRec_eq (k x y : Nat) : parityRec k x y = parityPow k x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    change (parityRec k x y && parityRec k (x / 4096^(2^k)) (y / 2^(2^k))) = _
    rw [ih, ih]
    rfl

noncomputable def parityRec1792 (x y : Nat) : Bool :=
  parityRec 10 x y && parityRec 9 (x / 4096^1024) (y / 2^1024) &&
    parityRec 8 (x / 4096^1536) (y / 2^1536)

theorem parityRec1792_eq (x y : Nat) : parityRec1792 x y = parity1792 x y := by
  simp only [parityRec1792, parity1792, parityRec_eq]

noncomputable def checkParitiesRec (ss : List Nat) : List Nat → Bool :=
  List.rec (fun cs => match cs with | [] => true | _ => false)
    (fun s _ next cs => match cs with
      | [] => false
      | c :: cs => parityRec1792 s c && next cs) ss

theorem checkParitiesRec_eq (ss cs : List Nat) :
    checkParitiesRec ss cs = checkParities ss cs := by
  induction ss generalizing cs with
  | nil => cases cs <;> rfl
  | cons s ss ih =>
    cases cs with
    | nil => rfl
    | cons c cs =>
      change (parityRec1792 s c && checkParitiesRec ss cs) = _
      rw [parityRec1792_eq, ih]
      rfl

theorem checksRec_sound (a c s w : List Nat) (t : Tree)
    (hv : Valid t) (hf : flatten t = w)
    (hs : checkSumsRec t a s = true) (hp : checkParitiesRec s c = true) :
    Wide.checkRows 1792 a w c = true := by
  rw [checkSumsRec_eq] at hs
  rw [checkParitiesRec_eq] at hp
  exact checks_sound a c s w t hv hf hs hp

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts

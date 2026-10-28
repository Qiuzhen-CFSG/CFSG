module

public import Theory.GroupTheory.Amalgam.SylowRigidity

/-!
# Finite coordinate certificates for overlap-twist factorization

A finite table is kept separate from its realization in actual groups.
A certificate consists of permutations of the two endpoint row sets and the
overlap row set, with multiplication and both embedding squares checked.
Completeness is a finite assertion about multiplication-preserving overlap
permutations. A realization transports the certificate to genuine endpoint
automorphisms and proves the literal `FactorsThrough` assertion.

This separates the independent coordinate-comparison and finite-enumeration
arguments used for the full binary G₂ amalgam. No group law or realization is
postulated for an arbitrary table, and the certificate is an explicit input.
-/

@[expose] public section
namespace Theory.GroupTheory.RankTwoAmalgam

structure FiniteTable (nL nB nR : ℕ) where
  leftMul : Fin nL → Fin nL → Fin nL
  middleMul : Fin nB → Fin nB → Fin nB
  rightMul : Fin nR → Fin nR → Fin nR
  left : Fin nB → Fin nL
  right : Fin nB → Fin nR

namespace FiniteTable
variable {nL nB nR : ℕ} (T : FiniteTable nL nB nR)

/-- Coordinate bijections, their multiplication laws, and both literal squares. -/
structure Realization {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R) where
  left : Fin nL ≃ L
  middle : Fin nB ≃ B
  right : Fin nR ≃ R
  left_mul : ∀ i j, left (T.leftMul i j) = left i * left j
  middle_mul : ∀ i j, middle (T.middleMul i j) = middle i * middle j
  right_mul : ∀ i j, right (T.rightMul i j) = right i * right j
  left_overlap : ∀ i, left (T.left i) = α.left (middle i)
  right_overlap : ∀ i, right (T.right i) = α.right (middle i)

/-- All fields are equalities between explicitly finite permutations and tables. -/
structure TwistWitness (d : Equiv.Perm (Fin nB)) where
  left : Equiv.Perm (Fin nL)
  right : Equiv.Perm (Fin nR)
  middleLeft : Equiv.Perm (Fin nB)
  middleRight : Equiv.Perm (Fin nB)
  left_mul : ∀ i j, left (T.leftMul i j) = T.leftMul (left i) (left j)
  right_mul : ∀ i j, right (T.rightMul i j) = T.rightMul (right i) (right j)
  left_overlap : ∀ i, left (T.left i) = T.left (middleLeft i)
  right_overlap : ∀ i, right (T.right i) = T.right (middleRight i)
  factors : ∀ i, d i = middleRight.symm (middleLeft i)

/-- The finite completeness obligation, with no actual-group recognition assumed. -/
def TwistsVerified : Prop :=
  ∀ d : Equiv.Perm (Fin nB),
    (∀ i j, d (T.middleMul i j) = T.middleMul (d i) (d j)) →
      Nonempty (T.TwistWitness d)

end FiniteTable

end Theory.GroupTheory.RankTwoAmalgam

public section
namespace Theory.GroupTheory.RankTwoAmalgam.FiniteTable

private def autOfCoordinates {n : ℕ} {G : Type*} [Group G]
    (e : Fin n ≃ G) (mul : Fin n → Fin n → Fin n)
    (hmul : ∀ i j, e (mul i j) = e i * e j)
    (a : Equiv.Perm (Fin n))
    (ha : ∀ i j, a (mul i j) = mul (a i) (a j)) : MulAut G where
  toEquiv := e.symm.trans (a.trans e)
  map_mul' x y := by
    obtain ⟨i, rfl⟩ := e.surjective x
    obtain ⟨j, rfl⟩ := e.surjective y
    change e (a (e.symm (e i * e j))) = e (a (e.symm (e i))) * e (a (e.symm (e j)))
    rw [← hmul, e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply, ha, hmul]

private theorem autOfCoordinates_apply {n : ℕ} {G : Type*} [Group G]
    (e : Fin n ≃ G) (mul : Fin n → Fin n → Fin n)
    (hmul : ∀ i j, e (mul i j) = e i * e j)
    (a : Equiv.Perm (Fin n))
    (ha : ∀ i j, a (mul i j) = mul (a i) (a j)) (i : Fin n) :
    autOfCoordinates e mul hmul a ha (e i) = e (a i) :=
  congrArg (fun j => e (a j)) (e.symm_apply_apply i)

private def autOfSquare {B L : Type*} [Group B] [Group L]
    (i : B →* L) (hi : Function.Injective i) (f : B ≃ B) (a : MulAut L)
    (h : ∀ b, a (i b) = i (f b)) : MulAut B where
  toEquiv := f
  map_mul' x y := by
    apply hi
    calc
      i (f (x * y)) = a (i (x * y)) := (h (x * y)).symm
      _ = a (i x) * a (i y) := by rw [map_mul, map_mul]
      _ = i (f x) * i (f y) := congrArg₂ (· * ·) (h x) (h y)
      _ = i (f x * f y) := (i.map_mul _ _).symm

variable {nL nB nR : ℕ} {T : FiniteTable nL nB nR}
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R}

/-- A realized finite certificate constructs actual endpoint extension witnesses. -/
theorem Realization.factorsThrough (E : T.Realization α)
    (hi : Function.Injective α.left) (hj : Function.Injective α.right)
    (hverified : T.TwistsVerified) (d : MulAut B) : FactorsThrough α d := by
  let p : Equiv.Perm (Fin nB) := E.middle.trans (d.toEquiv.trans E.middle.symm)
  have hp (i : Fin nB) : E.middle (p i) = d (E.middle i) :=
    E.middle.apply_symm_apply _
  have hpmul (i j : Fin nB) : p (T.middleMul i j) = T.middleMul (p i) (p j) := by
    apply E.middle.injective
    rw [hp, E.middle_mul, map_mul, E.middle_mul, hp, hp]
  obtain ⟨w⟩ := hverified p hpmul
  let a := autOfCoordinates E.left T.leftMul E.left_mul w.left w.left_mul
  let c := autOfCoordinates E.right T.rightMul E.right_mul w.right w.right_mul
  let u := E.middle.symm.trans (w.middleLeft.trans E.middle)
  let v := E.middle.symm.trans (w.middleRight.trans E.middle)
  have hu (i : Fin nB) : u (E.middle i) = E.middle (w.middleLeft i) :=
    congrArg (fun j => E.middle (w.middleLeft j)) (E.middle.symm_apply_apply i)
  have hv (i : Fin nB) : v (E.middle i) = E.middle (w.middleRight i) :=
    congrArg (fun j => E.middle (w.middleRight j)) (E.middle.symm_apply_apply i)
  have ha (b : B) : a (α.left b) = α.left (u b) := by
    obtain ⟨i, rfl⟩ := E.middle.surjective b
    rw [hu, ← E.left_overlap, ← E.left_overlap]
    exact (autOfCoordinates_apply E.left T.leftMul E.left_mul w.left w.left_mul _).trans
      (congrArg E.left (w.left_overlap i))
  have hc (b : B) : c (α.right b) = α.right (v b) := by
    obtain ⟨i, rfl⟩ := E.middle.surjective b
    rw [hv, ← E.right_overlap, ← E.right_overlap]
    exact (autOfCoordinates_apply E.right T.rightMul E.right_mul w.right w.right_mul _).trans
      (congrArg E.right (w.right_overlap i))
  let l := autOfSquare α.left hi u a ha
  let r := autOfSquare α.right hj v c hc
  refine ⟨l, r, ⟨a, ha⟩, ⟨c, hc⟩, ?_⟩
  apply MulEquiv.ext
  intro b
  obtain ⟨i, rfl⟩ := E.middle.surjective b
  apply r.injective
  change r (d (E.middle i)) = r (r.symm (l (E.middle i)))
  rw [r.apply_symm_apply, ← hp]
  change v (E.middle (p i)) = u (E.middle i)
  rw [hv, hu, w.factors, w.middleRight.apply_symm_apply]

end Theory.GroupTheory.RankTwoAmalgam.FiniteTable

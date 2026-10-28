module

public import Theory.SpecificGroups.ONan.E9A4.Data

/-!
# Projective separation of the 108 candidate matrices

The first five entries of the first row distinguish the matrix table up to
scalar. Kernel reduction checks these small fingerprints and their agreement
with the full matrices. Consequently equality up to scalar forces equal
coordinates, independently of the pending word-realization and multiplication
certificates. Sources and data generation are recorded in `source/README.md`.
-/

public section
namespace ONan.E9A4.Data
open Theory.SpecificGroups.E9A4 (Coord)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem firstRow_spec : ∀ (c : Coord) (j : Fin 5),
    table c 0 ⟨j.val, by omega⟩ = firstRow c j := by
  decide +kernel

private def rowNat (n j : ℕ) : ℕ :=
  (24297733517253377068203382703311361616451810799878075423452988651642232516749646314011118110986047990044955497153889384160824296136464974177380810166905314474159395476243230794221760557933132696804838875115136330420792975375352106617732479438500397327921786709260922754756765682429613718401503042787980601450157469998571999117650519223580203298284105302753132643912285392542228667931013955231674296427807461796495396202903413377580840151980757134234176587210578264667540109828100076142593 >>> (3 * (5 * n + j))) % 8

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rowNat_spec : ∀ (c : Coord) (j : Fin 5),
    (rowNat (index c).val j.val : ZMod 7) = firstRow c j := by
  decide +kernel

open ONan.Simplicity.Seven.Certificate in
private def rowsEqual (n m s : ℕ) : Bool :=
  checkAll (fun j => rowNat n j % 7 == (s * rowNat m j) % 7) 5

open ONan.Simplicity.Seven.Certificate in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem separationCheck :
    checkAll (fun n => checkAll (fun m => checkAll
      (fun s => !rowsEqual n m s || n == m) 7) 108) 108 = true := by
  decide +kernel

open ONan.Simplicity.Seven.Certificate in
theorem firstRow_separates (c d : Coord) (s : ZMod 7)
    (h : ∀ j, firstRow c j = s * firstRow d j) : c = d := by
  have hc := (checkAll_spec _ _).mp separationCheck (index c).val (index c).isLt
  have hd := (checkAll_spec _ _).mp hc (index d).val (index d).isLt
  have hs := (checkAll_spec _ _).mp hd s.val s.val_lt
  have hr : rowsEqual (index c).val (index d).val s.val = true := by
    apply (checkAll_spec _ _).mpr
    intro j hj
    apply beq_iff_eq.mpr
    apply (ZMod.natCast_eq_natCast_iff' _ _ 7).mp
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, rowNat_spec c ⟨j, hj⟩, rowNat_spec d ⟨j, hj⟩]
    exact h ⟨j, hj⟩
  simp only [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hs
  obtain ⟨⟨a, b⟩, k⟩ := c
  obtain ⟨⟨a', b'⟩, k'⟩ := d
  have ha : a = a' := Fin.ext (by simp only [index] at hs; omega)
  have hb : b = b' := Fin.ext (by simp only [index] at hs; omega)
  have hk : k = k' := Fin.ext (by simp only [index] at hs; omega)
  subst a'; subst b'; subst k'
  rfl

/-- The candidate matrices are pairwise distinct even in the projective quotient. -/
theorem table_separates (c d : Coord) (s : ZMod 7)
    (h : table c = s • table d) : c = d := by
  apply firstRow_separates c d s
  intro j
  have he := congrFun (congrFun h 0) (⟨j.val, by omega⟩ : Fin 45)
  change table c 0 ⟨j.val, by omega⟩ = s * table d 0 ⟨j.val, by omega⟩ at he
  simpa only [firstRow_spec] using he

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem table_zero : table ((0, 0), 0) = 1 := by
  have h : ∀ p : Fin 45 × Fin 45,
      table ((0, 0), 0) p.1 p.2 = if p.1 = p.2 then 1 else 0 := by
    decide +kernel
  exact Matrix.ext (fun i j => by simpa only [Matrix.one_apply] using h (i, j))

end ONan.E9A4.Data

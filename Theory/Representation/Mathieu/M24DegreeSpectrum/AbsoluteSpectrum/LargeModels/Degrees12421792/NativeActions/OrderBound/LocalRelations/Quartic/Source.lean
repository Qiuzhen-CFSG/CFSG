module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Contracts

/-!
# The square relation and signed source splitting

The original relation `a² = 1` permits inverse-a normalization without changing
word evaluation. This justifies every normalized cyclic split used by the
quartic certificate, including splits of the two inverse commutators. Critical
pairs are compared by two contextual rewrites of their common word, so both
suffix overlaps and containment are covered.

Source: John Bray's ATLAS M24G1-P1 and M24G1-max8W1. The untrusted candidate
is retained in `../source/quartic-candidate.json`; see `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations.Quartic.Certificate
open Subgroup.CosetWordCertificate Replay

/-- The four literal signed letters, shared by the bounded certificate blocks. -/
def letterA : Letter (Fin 2) := (0, true)
def letterB : Letter (Fin 2) := (1, true)
def letterC : Letter (Fin 2) := (1, false)
def letterD : Letter (Fin 2) := (0, false)

def normalize (w : Word (Fin 2)) : Word (Fin 2) :=
  w.map fun s => if s.1 = 0 then (0, true) else s

theorem inverse_a : (generator 0)⁻¹ = generator 0 := by
  have ha : generator 0 ^ 2 = 1 := generator_relations 0
  apply mul_left_cancel (a := generator 0)
  simp [← pow_two, ha]

theorem eval_normalize (w : Word (Fin 2)) :
    eval generator (normalize w) = eval generator w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    obtain ⟨i, sign⟩ := s
    fin_cases i <;> cases sign <;>
      simp [normalize, eval_cons, ← ih, inverse_a]

theorem normalized_split (i : Fin 7) (u v : Word (Fin 2))
    (inverse : Bool) (offset : Nat)
    (hc : normalize (variant (sourceLetters i) inverse offset) =
      u ++ normalize (FreeGroup.invRev v)) :
    eval generator u = eval generator v := by
  have hh := eval_variant_one generator (sourceLetters i) inverse offset
    (sourceLetters_eq_one i)
  rw [← eval_normalize, hc, eval_append, eval_normalize, eval_invRev,
    mul_inv_eq_one] at hh
  exact hh

theorem seed_square : eval generator [(0, true), (0, true)] = eval generator [] := by
  simpa [eval_cons, pow_two] using (show generator 0 ^ 2 = 1 from generator_relations 0)

theorem seed_cube : eval generator [(1, true), (1, true)] =
    eval generator [(1, false)] := by
  have hb : generator 1 ^ 3 = 1 := generator_relations 1
  simpa [eval_cons, pow_succ] using (mul_eq_one_iff_eq_inv.mp hb)

theorem seed_inverse_cube : eval generator [(1, false), (1, false)] =
    eval generator [(1, true)] := by
  have hb := congrArg Inv.inv seed_cube
  simpa [eval_cons, mul_inv_rev] using hb

/-- Two valid contextual rewrites of the same word give an equation between
outputs. In particular the second redex may lie entirely inside the first. -/
theorem common_rewrites (db : Database) (n : Nat) (w u v : Word (Fin 2))
    (s t : Nat × Nat) (h : ValidBefore generator db n)
    (hs : s.1 < n) (ht : t.1 < n)
    (hc : rewriteAt db w s = some u) (hd : rewriteAt db w t = some v) :
    eval generator u = eval generator v :=
  (rewriteAt_sound generator db w s (h s.1 hs) hc).symm.trans
    (rewriteAt_sound generator db w t (h t.1 ht) hd)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations.Quartic.Certificate

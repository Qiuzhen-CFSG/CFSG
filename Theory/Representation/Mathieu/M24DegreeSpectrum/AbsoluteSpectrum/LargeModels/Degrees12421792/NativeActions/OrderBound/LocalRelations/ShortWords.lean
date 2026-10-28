module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalPresentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.WordCalculus

/-!
# Short source words for the actual max8 subgroup

The commutator relator gives `e^12 = 1`, so the literal conjugator
`e^11 * c^7` can be shortened to `e⁻¹ * c^7`. The evaluation bridge
retains the literal ATLAS marking and applies to every fixed local relator.
This is a word-length reduction, not a proof of the remaining local identities.

Source: John Bray, ATLAS M24G1-P1 and M24G1-max8W1; see
`../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations
open Subgroup.CosetWordCertificate

def shortC : UniversalGroup := generator 1 * generator 0

def shortE : UniversalGroup := (generator 1)⁻¹ * generator 0 * generator 1 * generator 0

theorem shortE_pow_twelve : shortE ^ 12 = 1 := by
  let a := generator 0
  let b := generator 1
  have ha : a ^ 2 = 1 := generator_relations 0
  have hai : a⁻¹ = a := by
    apply mul_left_cancel (a := a)
    simp [← pow_two, ha]
  have hr : (b * a * b⁻¹ * a⁻¹) ^ 12 = 1 := signed_generator_relations 3
  have hx : b⁻¹ * (b * a * b⁻¹ * a⁻¹)⁻¹ * b = shortE := by
    change _ = b⁻¹ * a * b * a
    simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one, hai]
  rw [← hx]
  have hp := conj_pow (a := b⁻¹) (b := (b * a * b⁻¹ * a⁻¹)⁻¹) (i := 12)
  simpa only [inv_inv, inv_pow, hr, inv_one, mul_one, inv_mul_cancel] using hp

theorem shortE_pow_eleven : shortE ^ 11 = shortE⁻¹ := by
  calc
    shortE ^ 11 = (shortE ^ 11 * shortE) * shortE⁻¹ := by simp [mul_assoc]
    _ = shortE⁻¹ := by rw [← pow_succ, shortE_pow_twelve, one_mul]

def shortBoundLetters (s : Fin 2) : Word (Fin 2) :=
  let a : Word (Fin 2) := [(0, true)]
  let c : Word (Fin 2) := [(1, true), (0, true)]
  let e : Word (Fin 2) := [(1, false), (0, true), (1, true), (0, true)]
  if s = 0 then a else
    FreeGroup.invRev e ++ powerLetters c 7 ++ powerLetters e 3 ++
      FreeGroup.invRev (powerLetters c 7) ++ e

theorem eval_shortBoundLetters (s : Fin 2) :
    eval generator (shortBoundLetters s) = boundGenerator s := by
  have hb : generator 1 ^ 3 = 1 := generator_relations 1
  have hbi : (generator 1)⁻¹ = generator 1 ^ 2 := by
    apply mul_left_cancel (a := generator 1)
    rw [mul_inv_cancel, ← pow_succ', hb]
  have he : ((generator 1 * (generator 1 * generator 0)) *
      (generator 1 * generator 0)) = shortE := by
    simp only [shortE, hbi, pow_two, mul_assoc]
  fin_cases s
  · simp [shortBoundLetters, eval_cons, boundGenerator, subgroupWord]
  · rw [shortBoundLetters, if_neg (by decide)]
    simp only [eval_append, eval_invRev, eval_powerLetters, eval_cons,
      ↓reduceIte, eval_nil, mul_one]
    change shortE⁻¹ * shortC ^ 7 * shortE ^ 3 * (shortC ^ 7)⁻¹ * shortE = _
    change _ = ((_ ^ 11 * shortC ^ 7) * _ ^ 3 * (_ ^ 11 * shortC ^ 7)⁻¹)
    rw [he, shortE_pow_eleven, mul_inv_rev, inv_inv]
    simp only [mul_assoc]

/-- Expanded short words for precisely the nine fixed candidate relations. -/
def shortLocalRelator (i : Fin 9) : Word (Fin 2) :=
  Replay.expand shortBoundLetters (localRelatorLetters i)

/-- The shortening preserves every literal local-relator value in the source group. -/
theorem eval_shortLocalRelator (i : Fin 9) :
    eval generator (shortLocalRelator i) = eval boundGenerator (localRelatorLetters i) := by
  rw [shortLocalRelator, Replay.eval_expand]
  congr 1
  exact funext eval_shortBoundLetters

/-- Actual local-word consumer for any subsequently checked source-word replay. -/
theorem localRelator_of_short_replay (i : Fin 9) (db : Replay.Database) (n : Nat)
    (ss : List (Nat × Nat)) (hdb : Replay.ValidBefore generator db n)
    (hb : ss.all (fun s => decide (s.1 < n)) = true)
    (hc : Replay.replay db (shortLocalRelator i) ss = some []) :
    eval boundGenerator (localRelatorLetters i) = 1 := by
  rw [← eval_shortLocalRelator]
  exact (Replay.replay_prefix generator db n _ [] ss hdb hb hc).trans (eval_nil _)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations

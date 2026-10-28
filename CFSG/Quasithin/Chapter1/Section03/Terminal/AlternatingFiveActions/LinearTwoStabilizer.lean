module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.LinearTwoStabilizer.ProjectiveTrace
public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.LinearTwoStabilizer.AlternatingFive
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
import Mathlib.Tactic.IntervalCases

/-!
# Inner action on A₅ in the prime-field PSL₂ model

For an actual subgroup A isomorphic to A₅, every ambient automorphism that
preserves A acts on it by conjugation by an element of A. The proof separates
an element of order five from its square using squared matrix trace, then
uses the explicit five-cycle test for outer automorphisms of A₅. Prime-field
semilinear coverage proves that every ambient automorphism preserves this
invariant. All field, diagonal and quotient actions refer to the concrete
matrix model.

The underlying argument works for every prime field of order greater than
five. The source wrapper retains all four restrictions in
`Section02.A312ExceptionalPrime`: prime and odd q, q² ≡ 1 modulo five, and
q ≡ 3 or 5 modulo eight. Transport along `ClassicalGroup.IsPSL` maps the
actual subgroup, applies the matrix result, and pulls its conjugator back.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, A.3.12(8), printed p.47, and the last paragraph
of the proof of Lemma 1.3.9(1), printed p.514.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearTwoStabilizer

/-- The intrinsic stabilizer assertion over a prime field of order greater than five. -/
theorem hasInnerStabilizerAction_primeField_gt_five {F : Type*} [Field F] [Finite F]
    {q : ℕ} (hq : q.Prime) (h5q : 5 < q) (hF : Nat.card F = q)
    (A : Subgroup (Theory.PSL2.Group F)) (e : A ≃* alternatingGroup (Fin 5)) :
    A.HasInnerStabilizerAction := by
  let : Fintype F := Fintype.ofFinite F
  have : Fact q.Prime := ⟨hq⟩
  have : CharP F q := charP_of_card_eq_prime (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F q]; omega
  have hfive : (5 : F) ≠ 0 := by
    intro h
    have hd : q ∣ 5 := (CharP.cast_eq_zero_iff F q 5).mp h
    have := Nat.le_of_dvd (by decide : 0 < 5) hd
    omega
  apply hasInnerStabilizerAction_of_orderFive_square_separation ?_ A e
  intro α x hx he
  apply projectiveTraceSquared_ne_square hfive x hx
  calc
    projectiveTraceSquared x = projectiveTraceSquared (α x) :=
      (projectiveTraceSquared_aut_prime hq hF hchar (by omega) α x).symm
    _ = projectiveTraceSquared (x ^ 2) := congrArg projectiveTraceSquared he

/-- A.3.12(8)'s exact prime and congruence restrictions imply the intrinsic
A₅ stabilizer assertion needed in the proof of 1.3.9(1). -/
theorem hasInnerStabilizerAction_primeField {F : Type*} [Field F] [Finite F]
    {q : ℕ} (hq : Section02.A312ExceptionalPrime q) (hF : Nat.card F = q)
    (A : Subgroup (Theory.PSL2.Group F)) (e : A ≃* alternatingGroup (Fin 5)) :
    A.HasInnerStabilizerAction := by
  have h5q : 5 < q := by
    have hp := hq.1
    have hmod := hq.2.2.1
    by_contra h
    have hle : q ≤ 5 := by omega
    interval_cases q <;> norm_num at hmod <;> norm_num at hp
  exact hasInnerStabilizerAction_primeField_gt_five hq.1 h5q hF A e

/-- Transport carries the actual subgroup through the chosen classical model,
then carries the inner conjugator back to the original ambient group. -/
theorem hasInnerStabilizerAction_of_isPSL {Q : Type*} [Group Q] {q : ℕ}
    (hq : Section02.A312ExceptionalPrime q) (hQ : ClassicalGroup.IsPSL Q 2 q)
    (A : Subgroup Q) (e : A ≃* alternatingGroup (Fin 5)) :
    A.HasInnerStabilizerAction := by
  obtain ⟨F, hfield, hfinite, hF, ⟨f⟩⟩ := hQ
  apply Subgroup.HasInnerStabilizerAction.of_map f
  exact hasInnerStabilizerAction_primeField hq hF (A.map f.toMonoidHom)
    ((f.subgroupMap A).symm.trans e)

end CFSG.Quasithin.Chapter1.Terminal.LinearTwoStabilizer

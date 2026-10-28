module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.RankOneModels
public import CFSG.KnownSimple.ClassicalModels
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.RankOne
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.OddComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups.CentralCover

/-!
# Small symplectic and orthogonal proper Sylow overgroups

The actual rank-one symplectic carrier is PSL₂, and the minus-four carrier
over a field of order 2^a is PSL₂ over GF(2^(2a)). The checked polar action
identifies the commutator of PSp₄(2) with A₆. These equivalences give the
proper Sylow-overgroup bound, including the genuine small derived endpoint.
The odd orthogonal comparison transports any established symplectic bound
at the same rank and field; it does not supply the higher-rank bound itself.

Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85), and the actual
classical carrier comparisons of GLS3 §2.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- The rank-one symplectic alias, including the binary field. -/
theorem properSylowFittingBound_psp_one (F : Type*) [Field F] [Finite F]
    (a : ℕ) (ha : 0 < a) (hF : Nat.card F = 2 ^ a) :
    ProperSylowFittingBound (ClassicalGroup.PSp 1 F) :=
  properSylowFittingBound_psl2 F a ha hF
    Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv

/-- Transport through projection off the odd quadratic space's polar radical. -/
theorem properSylowFittingBound_odd_of_psp (F : Type*) [Field F] [Finite F]
    (r a : ℕ) (hr : 0 < r) (hF : Nat.card F = 2 ^ a)
    (h : ProperSylowFittingBound (ClassicalGroup.PSp r F)) :
    ProperSylowFittingBound (ClassicalOrthogonal.POmegaOdd r F) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact properSylowFittingBound_of_equiv
    (ClassicalOrthogonal.TheoremDRootNormalizer.oddProjectiveEquivPSp hr) h

/-- The odd rank-one alias is covered by the same concrete PSL₂ theorem. -/
theorem properSylowFittingBound_odd_one (F : Type*) [Field F] [Finite F]
    (a : ℕ) (ha : 0 < a) (hF : Nat.card F = 2 ^ a) :
    ProperSylowFittingBound (ClassicalOrthogonal.POmegaOdd 1 F) :=
  properSylowFittingBound_odd_of_psp F 1 a (by decide) hF
    (properSylowFittingBound_psp_one F a ha hF)

/-- The minus-four alias uses the actual quadratic extension field. -/
theorem properSylowFittingBound_minus_two (F : Type*) [Field F] [Finite F]
    (a : ℕ) (ha : 0 < a) (hF : Nat.card F = 2 ^ a) :
    ProperSylowFittingBound (ClassicalGroup.POmegaMinus 2 F) :=
  properSylowFittingBound_psl2 (GaloisField 2 (2 * a)) (2 * a) (by omega)
    (GaloisField.card 2 (2 * a) (by omega))
    (ClassicalOrthogonal.TheoremDRootNormalizer.minusTwoEquivPSL F ha hF)

/-- The genuine commutator carrier PSp₄(2)′, not the full nonsimple group. -/
theorem properSylowFittingBound_binary_symplectic_derived :
    ProperSylowFittingBound (commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  apply properSylowFittingBound_of_equiv
    Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  intro S X hSX hX
  exact AlternatingSix.ProperSylowOvergroups.centralCover_fitting_bound
    (MonoidHom.id _) Function.surjective_id (by simp) S X hSX hX

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

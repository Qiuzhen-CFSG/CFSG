module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.SymplecticOrthogonal.LowRanks
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Proper Sylow overgroups of nonbinary PSp₄ and odd orthogonal rank two

Root extraction places every proper Sylow overgroup in a conjugate of the
point or plane parabolic. Each parabolic has self-centralizing two-core,
which lies in the specified Sylow subgroup. Restriction therefore gives
F*(X) = O₂(X) even when X does not contain the full Borel. Conjugation and
the actual projective quotient equivalence return the result to PSp₄.
The odd quadratic projection gives the same bound for PΩ₅.

Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85); GLS3 2.6.5(e).
The two imported geometric calculations prove placement and the centralizer
bound separately; neither is an additional premise of the results here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
open Theory.SpecificGroups.SymplecticFour

/-- The full symplectic matrix group over every nonbinary field of order 2^a. -/
theorem properSylowFittingBound_sp_four (F : Type*) [Field F] [Finite F]
    [CharP F 2] (a : ℕ) (ha : 1 < a) (hF : Nat.card F = 2 ^ a) :
    ProperSylowFittingBound (Sp F) := by
  intro S X hSX hX
  have htwo : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ) ^ 1 < 2 ^ a from Nat.pow_lt_pow_right (by decide) ha)
  obtain ⟨g, hg⟩ := ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover
    htwo S X hSX hX
  let e := MulAut.conj g
  let Y := X.map e.toMonoidHom
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRY : (R : Subgroup (Sp F)) ≤ Y := map_mono hSX
  have hfit : generalizedFitting Y = pCore 2 Y := by
    rcases hg with hp | hp
    · exact generalizedFitting_eq_pCore_of_sylow_overgroup R Y pointParabolic
        hRY hp (pointParabolic_selfCentralizing_core hF ha)
    · exact generalizedFitting_eq_pCore_of_sylow_overgroup R Y planeParabolic
        hRY hp (planeParabolic_selfCentralizing_core hF ha)
  let eX : X ≃* Y := e.subgroupMap X
  have he := congrArg (Subgroup.map eX.symm.toMonoidHom) hfit
  rw [map_generalizedFitting_equiv eX.symm, pCore_map_iso 2 eX.symm] at he
  rw [he]
  exact le_sup_left

/-- The exact projective symplectic carrier in rank two and its simple field range. -/
theorem properSylowFittingBound_psp_two (F : Type*) [Field F] [Finite F]
    (a : ℕ) (ha : 1 < a) (hF : Nat.card F = 2 ^ a) :
    ProperSylowFittingBound (ClassicalGroup.PSp 2 F) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact properSylowFittingBound_of_equiv EvenProjective.equiv.symm
    (properSylowFittingBound_sp_four F a ha hF)

/-- Odd orthogonal rank two, with the actual polar-radical projection. -/
theorem properSylowFittingBound_odd_two (F : Type*) [Field F] [Finite F]
    (a : ℕ) (ha : 1 < a) (hF : Nat.card F = 2 ^ a) :
    ProperSylowFittingBound (ClassicalOrthogonal.POmegaOdd 2 F) :=
  properSylowFittingBound_odd_of_psp F 2 a (by decide) hF
    (properSylowFittingBound_psp_two F a ha hF)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

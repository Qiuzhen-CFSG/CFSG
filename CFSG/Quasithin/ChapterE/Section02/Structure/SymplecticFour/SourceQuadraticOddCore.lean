module

public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.OddCore
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceQuadraticExclusion

/-!
# Unconditional odd and Fitting cores of the original E.2.7 pair

The original minimal-parabolic geometry supplies irreducibility, trivial
two-core and the exclusion of every compatible quadratic form. Averaging
over an odd normal subgroup would contradict that exclusion. Thus the odd
core and Fitting subgroup of the literal original pair vanish, as does the
Fitting subgroup of its normal F-transvection closure.

This removes the odd-Fitting premise in the source application of
Aschbacher--Smith G.4.9, printed p.341, without assuming primitivity of a
restriction or excluding the transvection-containing branch.
-/

public noncomputable section

open Subgroup

namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour

open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original pair, including its transvection-containing branch, has
trivial odd core and Fitting subgroup. The same holds for the Fitting subgroup
of its literal normal transvection closure. No new source premise remains. -/
theorem source_geometry_fitting_cores_eq_bot {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP = ⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F ≃* L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom) = unipotent)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G) ≤ normalizer (V : Set G)) (hr : 2 < Nat.card V) :
    let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    pPrimeCore 2 H = ⊥ ∧ fittingSubgroup H = ⊥ ∧
      fittingSubgroup (transvectionClosure H) = ⊥ := by
  dsimp only
  let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
  obtain ⟨_,_,_,hi,h2⟩ := source_geometry hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr
  have hno : ∀ Q : QuadraticForm F (Vector F), Q.polarBilin = form F →
      ¬ ∀ g ∈ H, ∀ v : Vector F, Q (g • v) = Q v := by
    intro Q hQ
    exact source_geometry_quadratic_exclusion hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr Q hQ
  exact ⟨oddCore_eq_bot_of_no_invariant_quadratic H hi hno,
    fitting_eq_bot_of_no_invariant_quadratic H hi h2 hno,
    normal_fitting_eq_bot_of_no_invariant_quadratic H hi h2 hno (transvectionClosure H)⟩

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour

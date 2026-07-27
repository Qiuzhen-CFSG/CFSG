module

import Submission.FeitThompson.PFsection7.PFsection7_7
public import Submission.FeitThompson.PFsection7.PFsection7_6

noncomputable section

namespace Section7

universe v
universe u

@[expose] public def theorem_7_8_c_statement
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L H : Subgroup G)
    (K : G → Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (S : Finset (Section1.ClassFunction L))
    (τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L)
    (χ : Section1.ClassFunction G) : Prop :=
  hypothesis_7_6_statement A L H K T →
    agreesWithDadeTransform A L K τ →
    theorem_7_8_hypothesis L H T S τ ν ζ →
      Section1.IsIrreducibleCharacterOnGroup χ →
        orthogonalToImage S ν χ →
          theorem_7_8_c_projectionData A L H T τ ζ χ →
          (∀ x : L, (x : G) ∈ A →
            dadeProjection L K χ x =
              Section1.scalarProduct G (theorem_7_8_beta L H τ ζ) χ) ∧
            (Section5.cfNormSq (dadeProjectionOn A L K χ) : ℂ) =
              ((A.ncard : ℂ) / (Nat.card L : ℂ)) *
                (Section1.scalarProduct G (theorem_7_8_beta L H τ ζ) χ) ^ 2

/-- Peterfalvi `(7.9)`. -/


public theorem theorem_7_8_c
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L H : Subgroup G)
    (K : G → Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (S : Finset (Section1.ClassFunction L))
    (τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L)
    (χ : Section1.ClassFunction G) :
    theorem_7_8_c_statement A L H K T S τ ν ζ χ := by
  rw [theorem_7_8_c_statement]
  intro h76 hτ _h78 _hχ _horth hproj
  rcases hproj with
    ⟨n, η, d, c, henum, hbasis, hclass, hcoeff, hpoint, hnorm⟩
  have h77 := theorem_7_7 A L H K T η d τ χ c
    h76 hτ henum hbasis hclass hcoeff
  constructor
  · intro x hx
    rw [h77.1 x hx]
    exact hpoint x hx
  · exact h77.2.trans hnorm

end Section7

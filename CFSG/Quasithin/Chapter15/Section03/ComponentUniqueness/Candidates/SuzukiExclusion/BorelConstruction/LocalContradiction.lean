module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.BorelConstruction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion

/-!
# Applying the constructed Suzuki Borel to the local contradiction

The constructed relative normalizer discharges the Borel existence,
invariance, characteristic-two, marked-model and maximality premises of
`false_of_suzuki_borel_model`. That reduction then uses 15.3.33(1) to
identify the Borel with (M ∩ I) ∩ L₀ and bounds the literal conjugation
commutators in its two-core.

The concrete order-three automorphism detector and the earlier component
action hypotheses remain inputs belonging to the parent source assembly.
This application does not assert the full quotient exclusion of 15.3.34.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.34, printed p.1134; component-action inputs from 1.2.1(3)/A.3.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion
variable {G : Type*} [Group G] [Finite G]

/-- The local Suzuki contradiction with all Borel construction premises
discharged. The independent action detector is still explicit. -/
theorem false_of_suzuki_component_model
    (hact : ∀ m n : ℕ, 0 < m → (n = 1 ∨ n = 2) →
      DetectsThreeAutomorphisms (Subgroup.pi Set.univ
        (fun _ : Fin n => SuzukiBorelSubgroup m)))
    {Yplus S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (htheta : Yplus = theta (M ⊓ I))
    (hLI : L ≤ I) (hLM : ¬ L ≤ M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I)) (m : ℕ) (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m)
    (hSY : S ≤ normalizer (Yplus : Set G))
    (hYL : Yplus ≤ normalizer (L : Set G))
    (hindex : (normalizer (L.subgroupOf I : Set I)).index ≤ 2) : False := by
  obtain ⟨hL0N, B, hBL, hBN, hBF, hmodel, hmax⟩ :=
    exists_invariant_suzuki_orbit_borel hLI hI.1.2 P hP hL m hm e hSY hY hYL hindex
  exact false_of_suzuki_borel_model hact hI hSylow h25 hodd hSM hMI hY htheta hLI hLM
    hL0N hBL hBN hBF hmax hmodel

end CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion

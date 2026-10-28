module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.CubicCovers
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.Normalizer
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Complete

/-!
# The complete Ree covering branch of A.2.18

The original Case II counterexample has a selected odd prime dividing its
actual center. The complete torus and normalizer calculations in the literal
Ree fixed-point model show that every finite perfect cover has two-group
center. The selected prime must therefore be two, a contradiction. All
local-geometry and carrier-order premises are discharged by the model proofs.
Source: Aschbacher--Smith A.2.18, printed p.40, and I.1.3--4, pp.407--408.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] [IsQuasisimple G]

/-- The three-primary Ree possibility is impossible under the original counterexample hypotheses. -/
theorem caseII_reeF4_three_of_source
    (h : CounterexampleToTheoremA K G S 3) (ih : TheoremAOnProperSections K G)
    {m : ℕ} (hm : 1 ≤ m)
    (iso : Nonempty (G ⧸ center G ≃* ReeF4.Model m)) : False := by
  obtain ⟨e⟩ := iso
  have hd : 3 ∣ Nat.card (center G) := h.prime_dvd_center ih
  have hn := ReeF4.CentralCovers.OddPrimary.Three.Descent.not_three_dvd_kernel m hm
    (centralQuotientCover e)
  exact hn (by rwa [centralQuotientCover_ker])

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_reeF4_three
    (h : CounterexampleToTheoremA K G S 3) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup 3 (center G)) {m : ℕ} (hm : 1 ≤ m)
    (iso : Nonempty (G ⧸ center G ≃* ReeF4.Model m)) : False := by
  have _primary := hP
  exact caseII_reeF4_three_of_source h ih hm iso

/-- Every genuine ReeF4 quotient is excluded by its complete odd-primary cover calculation. -/
theorem caseII_reeF4_of_source {p : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {m : ℕ} (hm : 1 ≤ m)
    (iso : Nonempty (G ⧸ center G ≃* ReeF4.Model m)) : False := by
  obtain ⟨e⟩ := iso
  have hp2 := h.prime_eq_of_center_isPGroup ih
    (ReeF4.CentralCovers.OddPrimary.center_isPGroup_of_quotient_equiv m hm e)
  have ho := h.2.2.2.2.2.1
  rw [hp2] at ho
  exact (by decide : ¬ Odd (2 : ℕ)) ho

end CFSG.Quasithin.ChapterA.Section02.EvenLie

module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.WeakClosure.Generation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry

/-!
# The rank-one weak-closure contradiction on the original chosen module

The subgroup R₁ is literally the two-core of L₁T for the chosen invariant
flag, and M is the original N_G(L). A specified Sylow subgroup of the
outside H₁ has ambient image R₁. The proved E.3.19 specialization therefore
applies to the two ambient bounds C_G(C₁(R₁,V)) ≤ M and N_G(W₀(R₁,V)) ≤ M,
giving the contradiction in the first paragraph of 11.5.1.

The flag, outside witness, and preceding geometric bounds remain explicit.
Their construction belongs to the local-geometry and component reductions;
this module does not assert the full G₂ exclusion from the initial setup.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.2.2(3,5,6) and 11.5.1, printed pp.767--768,778--779.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The selected-witness form of the first contradiction in 11.5.1, on the
original V and actual R₁, with both ambient 11.2.2 bounds stated literally. -/
theorem rankOne_R1_weakClosure_impossible (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (flag : LocalGeometry.InvariantFlag c)
    (H₁ : Subgroup G) (P : Sylow 2 H₁)
    (hP : (P : Subgroup H₁).map H₁.subtype = flag.Ri 0)
    (hn : ChapterE.generationParameter H₁ = 1)
    (hout : ¬ H₁ ≤ normalizer (L : Set G))
    (hs : (1 : ℕ∞) < @ChapterE.globalS G _ V D.elementary)
    (hC : centralizer (ChapterE.weakCentralizer V (flag.Ri 0) 1 : Set G) ≤
      normalizer (L : Set G))
    (hN : normalizer (ChapterE.indexedWeakClosure V (flag.Ri 0) 0 : Set G) ≤
      normalizer (L : Set G)) : False := by
  let := D.elementary
  apply hout
  apply ChapterE.RankOneWeakClosure.le_of_parameter_eq_one P hn hs
  · simpa only [hP] using hC
  · simpa only [hP] using hN

/-- The component owner may supply the outside subgroup and its relative Sylow
existentially; E.3.19 discharges the remaining containment step. -/
theorem no_outside_rankOne_R1_witness (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (flag : LocalGeometry.InvariantFlag c)
    (hs : (1 : ℕ∞) < @ChapterE.globalS G _ V D.elementary)
    (hC : centralizer (ChapterE.weakCentralizer V (flag.Ri 0) 1 : Set G) ≤
      normalizer (L : Set G))
    (hN : normalizer (ChapterE.indexedWeakClosure V (flag.Ri 0) 0 : Set G) ≤
      normalizer (L : Set G)) :
    ¬ ∃ H₁ : Subgroup G, ¬ H₁ ≤ normalizer (L : Set G) ∧
      ChapterE.generationParameter H₁ = 1 ∧
      ∃ P : Sylow 2 H₁, (P : Subgroup H₁).map H₁.subtype = flag.Ri 0 := by
  rintro ⟨H₁, hout, hn, P, hP⟩
  exact D.rankOne_R1_weakClosure_impossible S flag H₁ P hP hn hout hs hC hN

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

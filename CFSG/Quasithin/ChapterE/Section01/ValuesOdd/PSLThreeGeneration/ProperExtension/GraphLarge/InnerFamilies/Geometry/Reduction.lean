module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.RootGeneration

/-!+# Two concrete witness constructions for inner-family generation

The split-torus route asks for a solvable overgroup of the full ambient
Sylow subgroup containing a mixing matrix. The other route asks for an
odd-prime subgroup normalized by the actual C_T(A), whose commutator with
the original inner four-group contains such a matrix. The checked root
calculation consumes either witness and forces the containing subgroup to
be the whole graph extension.

The four-group route uses the proved actor reductions: every nontrivial
inner actor in a large family has order four and contains the given inner
involution centralizing T. No subgroup or intersection is inserted into the
family. Both witness constructions remain explicit premises here.

Source: Aschbacher--Smith E.1.2, E.1.5 and E.1.14(7), printed pp.209--210,
214; Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

namespace InnerGenerationGeometry

/-- The split-torus construction must contain the full graph-extension Sylow. -/
@[expose] def SolvableMixing : Prop :=
  ∀ (T : Sylow 2 (graphExtension F)) (z : graphExtension F),
    orderOf z = 2 → z ∈ innerPart F →
    (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F)) →
    ∃ H : Subgroup (graphExtension F),
      (T : Subgroup (graphExtension F)) ≤ H ∧ Group.IsSolvable H ∧
        HasMixingElement F z H

/-- The odd-torus construction retains the original actor and its full ambient
Sylow centralizer. Its output is an explicit matrix in the actual commutator. -/
@[expose] def FourGroupOddMixing : Prop :=
  ∀ (T : Sylow 2 (graphExtension F)) (A : Subgroup (graphExtension F)),
    IsElementaryAbelian 2 A → Nat.card A = 4 →
    A ≤ (T : Subgroup (graphExtension F)) → A ≤ innerPart F →
    ∀ z : graphExtension F, orderOf z = 2 → z ∈ A →
    (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F)) →
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup (graphExtension F),
      IsPGroup r X ∧
      (T : Subgroup (graphExtension F)) ⊓ centralizer (A : Set (graphExtension F)) ≤
        normalizer (X : Set (graphExtension F)) ∧
      HasMixingElement F z ⁅X, A⁆

end InnerGenerationGeometry

open InnerGenerationGeometry

omit [IsSimpleGroup PSL(3,F)] in
/-- A solvable full-Sylow witness discharges the published generation input. -/
theorem innerCentralizerGeneration_of_solvable_mixing
    (hgeometry : SolvableMixing F) : InnerCentralizerGeneration F := by
  intro T Ω _ _ _ z hz hzI hTz M hCM _ hsol _
  obtain ⟨H, hTH, hs, hmix⟩ := hgeometry T z hz hzI hTz
  exact eq_top_of_mixing F z M hCM (hmix.mono F (hsol H hTH hs))

/-- The original large inner actor supplies exactly the four-group input of
the odd-torus construction; all the remaining controls are the literal ones
in `InnerCentralizerGeneration`. -/
theorem innerCentralizerGeneration_of_four_group_odd_mixing {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (hgeometry : FourGroupOddMixing F) : InnerCentralizerGeneration F := by
  intro T Ω hΩ hlarge hi z hz hzI hTz M hCM _ _ hcomm
  obtain ⟨A, hA, hAT, hne, hAI⟩ := hi
  have hfour := inner_actor_card_eq_four F hp ho hF hΩ hlarge hA hAT hne hAI
  have hzA := inner_actor_contains_central_involution F hp ho hF hΩ hlarge
    hA hAT hne hAI hzI (hz ▸ pow_orderOf_eq_one z) hTz
  obtain ⟨r, hr, hor, X, hX, hn, hmix⟩ :=
    hgeometry T A (hΩ.1 A hA) hfour hAT hAI z hz hzA hTz
  exact eq_top_of_mixing F z M hCM
    (hmix.mono F (hcomm A hA hAT r hr hor X hX hn))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge

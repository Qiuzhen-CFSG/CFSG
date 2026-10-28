module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.CentralizerRoute
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.SplitMonomial
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Transferring matrix mixing to the original eight-actor

The inner intersection of an outer eight-actor is an elementary four-group.
Ambient tau centralizes this intersection. Thus the existing odd-torus
mixing witness for that four-group is controlled by the commutator with the
original actor. No membership of the intersection in the family is used.
For fields of order one modulo four, the proved solvable full-Sylow mixing
construction already supplies the required generation.

Source: Aschbacher--Smith E.1.8, E.1.13 and E.1.14(7), pp.210--214;
the matrix generation calculation is in `InnerFamilies/Geometry/RootGeneration`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors
open InnerGenerationGeometry
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

omit [IsSimpleGroup PSL(3,F)] in
/-- A solvable full-Sylow mixing witness is independent of the actor size. -/
theorem centralizerGeometry_of_solvable_mixing
    (hmix : SolvableMixing F) : CentralizerGeometry F := by
  intro T Ω _ _ _ A _ _ _ _ z hz hzL _ hTz M hCM _ hsol _
  obtain ⟨H, hTH, hs, hm⟩ := hmix T z hz hzL hTz
  exact eq_top_of_mixing F z M hCM (hm.mono F (hsol H hTH hs))

/-- The odd-torus witness is applied to the inner four-group, while its
commutator is controlled by the original member of the source family. -/
theorem centralizerGeometry_of_four_group_odd_mixing
    (hmix : FourGroupOddMixing F) : CentralizerGeometry F := by
  intro T Ω hΩ _ _ A hA hAT _ hfour z hz hzL hzA hTz M hCM _ _ hodd
  let D := A ⊓ innerPart F
  let _ := hΩ.1 A hA
  have hD : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (show D ≤ A from inf_le_left)
  obtain ⟨r, hr, hor, X, hX, hn, hm⟩ :=
    hmix T D hD hfour (inf_le_left.trans hAT) inf_le_right z hz ⟨hzA, hzL⟩ hTz
  have htau : tau (T : Subgroup (graphExtension F)) A ≤
      (T : Subgroup (graphExtension F)) ⊓ centralizer (D : Set (graphExtension F)) := by
    intro t ht
    refine ⟨tau_le _ _ ht, mem_centralizer_iff.mpr ?_⟩
    intro d hd
    have hc := (mem_centralizerModulo_iff.mp ht).2 d hd.1
    rw [twoCore_eq_bot F, mem_bot] at hc
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  have hc : ⁅X, D⁆ ≤ M := (commutator_mono le_rfl inf_le_left).trans
    (hodd A hA hAT r hr hor X hX (htau.trans hn))
  exact eq_top_of_mixing F z M hCM (hm.mono F hc)

/-- The split residue class has no remaining matrix-generation premise. -/
theorem centralizerGeometry_of_card_mod_four_eq_one (hmod : Nat.card F % 4 = 1) :
    CentralizerGeometry F :=
  centralizerGeometry_of_solvable_mixing F
    (solvableMixing_of_card_mod_four_eq_one F hmod)

/-- Only the already owned odd-torus construction remains in the other
residue class. This is the geometry consumed by the centralizer route. -/
theorem centralizerGeometry_of_residue_mixing {p : ℕ}
    (ho : Odd p) (hF : Nat.card F = p)
    (hnonsplit : p % 4 = 3 → FourGroupOddMixing F) : CentralizerGeometry F := by
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨k, hk⟩ := ho
    omega
  rcases hmod with h | h
  · exact centralizerGeometry_of_card_mod_four_eq_one F (hF ▸ h)
  · exact centralizerGeometry_of_four_group_odd_mixing F (hnonsplit h)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors

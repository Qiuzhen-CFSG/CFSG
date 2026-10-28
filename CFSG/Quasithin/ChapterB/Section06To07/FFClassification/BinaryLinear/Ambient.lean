module

public import Theory.SpecificGroups.BinaryLinear.InvariantParabolicPair
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.IntrinsicParabolics
/-!
# Binary SL4 and SL5 normal supplements are not minimal parabolic

The two intrinsic Sylow-normalized flag stabilizers are transported through
the actual marking of the normal subgroup. Their proper Sylow supplements
contradict the unique-maximal-overgroup condition. This uses only the original
normal subgroup and Sylow, so it applies to every module row and imposes no
extra condition on the module centralizer.

Source: Aschbacher–Smith B.6.9, printed p.116.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G]

theorem not_minimalParabolic_of_binary_linear_supplement
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    {n : ℕ} (hn : n=4 ∨ n=5) (e : L ≃* SL(n,ZMod 2))
    (hgen : L ⊔ (T : Subgroup G) = ⊤) : ¬ IsMinimalParabolicOver T ⊤ := by
  let eL := e.trans (slEquivLinear n)
  let : Finite (LinearGroup n) := Finite.of_equiv L eL.toEquiv
  let S : Sylow 2 (LinearGroup n) := Classical.arbitrary _
  obtain ⟨P,Q,hPQ,hP,hQ,hSP,hSQ,hinv⟩ := exists_automorphism_invariant_parabolic_pair hn S
  exact not_minimalParabolic_of_intrinsic_parabolics T L eL hgen S P Q hPQ hP hQ hSP hSQ hinv
end CFSG.Quasithin.ChapterB

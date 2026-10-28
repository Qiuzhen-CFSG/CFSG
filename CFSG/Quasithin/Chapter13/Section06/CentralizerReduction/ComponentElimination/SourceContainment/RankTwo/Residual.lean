module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.Basic
public import Theory.GroupTheory.PResidual.QuasisimpleCubicGeneration

/-!
# The ordinary residual case of source 13.6.20

For actual K ∈ Y_z, perfectness comes from the local C-component condition.
The intrinsic cubic-generation theorem turns the ordinary residual outcome
of A.3.18, on the literal subgroup K ⊔ L_v, into θ(K ⊔ L_v) = K.
The established local cubic generation of L_v then gives L_v ≤ K.

This is one conditional case, not the complete rank-two branch. Applying
A.3.18 requires a C-component in this particular overgroup and a quasisimple
two-core quotient. The center-rank bound also remains explicit here. They
must be established from the genuine earlier source inputs; the projective
and diagonal exceptional cases must still be excluded using actual models.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
A.3.18, printed pp.51–53, and 13.6.20, printed p.931.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/-- The ordinary A.3.18 outcome on K L_v yields both assertions used in the
rank-two line of the source proof. No theta equality is an input. -/
theorem source_residual_case (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) (hr : primeRank 3 K = 2)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : primeRank 3 (center (K ⧸ pCore 2 K)) ≤ 1)
    (hres : K.subgroupOf (K ⊔ Lv L v) =
      primeToResidual 3 (K ⊔ Lv L v : Subgroup G))
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3) :
    closure {x : G | x ∈ K ⊔ Lv L v ∧ orderOf x = 3} = K ∧ Lv L v ≤ K := by
  let := Chapter1.mem_L_isPerfect hK.1.2
  let := hq
  have htheta := cubic_closure_eq_of_primeToResidual K (K ⊔ Lv L v)
    le_sup_left (by omega) hc hres
  exact ⟨htheta, (Lv_le_cubic_closure_sup K L v hcard).trans_eq htheta⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo

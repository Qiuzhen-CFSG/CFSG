module

public import CFSG.Quasithin.ChapterE.Section05.Generation

/-!
# Reduction to minimal E-members outside the generating subgroup

If the proposed generating subgroup contains the Sylow subgroup, control of
O²(K) implies control of K by the Sylow supplement identity. A contrary
E-member therefore contains a minimal contrary E-member. This finite-lattice
argument permits the structural part of E.5.2 to work only with these minimal
members, with A fixed. It does not assert irreducibility in the odd-prime case.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, E.5.2, printed p.243 (the choice of minimal K).
-/

open Subgroup Stellmacher CFSG.Quasithin.ChapterB
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- Minimality is among genuine rank-bounded E-members outside M, with A fixed. -/
@[expose] public def IsMinimalEscapingEMember (j : ℕ) (P A M K : Subgroup G) : Prop :=
  Minimal (fun L : Subgroup G => IsEMemberAt j P A L ∧ ¬ L ≤ M) K

/-- It suffices to control the residuals of minimal E-members outside the target. -/
public theorem eq_top_of_minimal_thompson_residuals
    (P : Sylow 2 G) (i j : ℕ) (hgen : IsEGenerated j G) (M : Subgroup G)
    (hN : normalizer (thompsonJ (P : Subgroup G) i : Set G) ≤ M)
    (hR : ∀ A K : Subgroup G, A ∈ thompsonFamily (P : Subgroup G) i →
      IsMinimalEscapingEMember j (P : Subgroup G) A M K →
      (pResidual 2 K).map K.subtype ≤ M) : M = ⊤ := by
  have hPM : (P : Subgroup G) ≤ M :=
    (P : Subgroup G).le_normalizer.trans
      ((normalizer_le_normalizer_thompsonJ _ i).trans hN)
  apply eq_top_of_thompson_residuals P i j hgen M hN
  intro A K hA hK
  have hKM : K ≤ M := by
    by_contra hnot
    obtain ⟨L, _, hL⟩ := exists_minimal_le_of_wellFoundedLT
      (fun L : Subgroup G => IsEMemberAt j (P : Subgroup G) A L ∧ ¬ L ≤ M)
      K ⟨hK, hnot⟩
    exact hL.1.2 (hL.1.1.1.le_of_residual_le hPM (hR A L hA hL))
  exact (map_le_range _ _).trans ((range_subtype K).le.trans hKM)

end CFSG.Quasithin.ChapterE

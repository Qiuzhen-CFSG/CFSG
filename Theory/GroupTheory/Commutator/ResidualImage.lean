module
public import Theory.GroupTheory.PResidual.NormalizedComparison
public import Theory.GroupTheory.PCoreRestriction

/-!
# Commuting images of a residual through a primary kernel

If A is p-perfect and the p-group kernel of f normalizes A, normalization
of its image lifts to normalization of A. Thus, when f(A) and f(B)
commute, [A,B] lies both in A and in the kernel. This normal p-subgroup
intersection lies in Oₚ(A).

The original 13.4.7 pair applies this to its literal action quotient after
identifying the action kernel with O₂(X). Its already proved exclusion
of the residual commutator bound then rules out commuting images.
Source: Aschbacher–Smith 13.4.7, printed p.900.
-/

public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

theorem commutator_le_pCoreIn_of_commuting_images {p : ℕ}
    (f : G →* H) (A B : Subgroup G) (hp : IsPPerfect p A)
    (hk : IsPGroup p f.ker) (hn : f.ker ≤ normalizer (A : Set G))
    (hc : ⁅A.map f,B.map f⁆ = ⊥) : ⁅A,B⁆ ≤ A.pCoreIn p := by
  have hBA : B ≤ normalizer (A : Set G) :=
    (map_le_normalizer_map_iff_of_pPerfect f A B hp hk hn).mp
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hcommA : ⁅A,B⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp hBA
  have hcommK : ⁅A,B⁆ ≤ f.ker := by
    apply (map_eq_bot_iff _).mp
    rwa [map_commutator]
  have hcore : f.ker.subgroupOf A ≤ pCore p A :=
    le_sSup ⟨inferInstance,hk.comap_subtype⟩
  intro x hx
  exact mem_map_of_mem A.subtype
    (hcore (show (⟨x,hcommA hx⟩ : A) ∈ f.ker.subgroupOf A from hcommK hx))
end Subgroup

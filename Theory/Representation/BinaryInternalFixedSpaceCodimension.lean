module

public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Action
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Rank

/-!
# The internal fixed-space dimension and supplement argument

Let V ≤ W be elementary abelian two-subgroups invariant under I = ⟨Xᵢ⟩.
If L ≤ I, the sum of the fixed codimensions on V is at most the fixed
codimension of L, and every C_W(Xᵢ) supplements V, then C_W(L) = C_W(I)
and C_W(L) supplements V.

Apply the fixed-space dimension theorem to V. Each generator supplement
identifies its codimensions on V and W; monotonicity under V ≤ W gives
the required dimension bound for W. Apply the same theorem to W. The two
equalities of dimensions now identify the L-codimensions, forcing the final
supplement by the relative-index criterion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.18,
printed p.81. These are only the dimension step's explicit hypotheses;
the source theorem must establish them separately.
-/

open Subgroup
namespace Representation.BinaryInternalFixedSpaceCodimension
variable {G ι : Type*} [Group G] [Finite G] [Fintype ι]

/-- Equality of internal fixed spaces and the resulting supplement. -/
public theorem fixed_eq_and_supplement (V W : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (X : ι → Subgroup G) (L : Subgroup G) (hVW : V ≤ W)
    (hV : (⨆ i, X i) ≤ normalizer (V : Set G))
    (hW : (⨆ i, X i) ≤ normalizer (W : Set G))
    (hL : L ≤ ⨆ i, X i)
    (hdim : (∑ i, (Nat.log 2 (Nat.card V) -
      Nat.log 2 (Nat.card ↥(V ⊓ centralizer (X i : Set G))))) ≤
      Nat.log 2 (Nat.card V) - Nat.log 2 (Nat.card ↥(V ⊓ centralizer (L : Set G))))
    (hsupp : ∀ i, W = (W ⊓ centralizer (X i : Set G)) ⊔ V) :
    W ⊓ centralizer (L : Set G) = W ⊓ centralizer ((⨆ i, X i : Subgroup G) : Set G) ∧
      W = (W ⊓ centralizer (L : Set G)) ⊔ V := by
  have hgen (i : ι) :
      Nat.log 2 (Nat.card V) - Nat.log 2 (Nat.card ↥(V ⊓ centralizer (X i : Set G))) =
        Nat.log 2 (Nat.card W) - Nat.log 2 (Nat.card ↥(W ⊓ centralizer (X i : Set G))) :=
    (rank_eq_iff_supplement V W (centralizer (X i : Set G)) hVW).mpr (hsupp i)
  obtain ⟨_, hVrank⟩ := fixed_eq_and_rank_eq_of_sum_le V X L hV hL hdim
  have hdimW : (∑ i, (Nat.log 2 (Nat.card W) -
      Nat.log 2 (Nat.card ↥(W ⊓ centralizer (X i : Set G))))) ≤
      Nat.log 2 (Nat.card W) - Nat.log 2 (Nat.card ↥(W ⊓ centralizer (L : Set G))) := by
    calc
      _ = ∑ i, (Nat.log 2 (Nat.card V) -
          Nat.log 2 (Nat.card ↥(V ⊓ centralizer (X i : Set G)))) :=
        Finset.sum_congr rfl fun i _ => (hgen i).symm
      _ ≤ _ := hdim.trans (rank_mono V W (centralizer (L : Set G)) hVW)
  obtain ⟨hfixed, hWrank⟩ := fixed_eq_and_rank_eq_of_sum_le W X L hW hL hdimW
  refine ⟨hfixed, (rank_eq_iff_supplement V W (centralizer (L : Set G)) hVW).mp ?_⟩
  rw [hVrank, hWrank]
  exact Finset.sum_congr rfl fun i _ => hgen i

end Representation.BinaryInternalFixedSpaceCodimension

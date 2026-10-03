module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Normality of a coprime centralizer complement

Let Q and V be normal subgroups of a finite group, with V≤Q centralizing Q.
For a Sylow p-subgroup T of order coprime to Q, suppose QT is normal and
V has no nontrivial T-fixed element. If T≤R and [Q,R]≤V, then
W=C_Q(T) is a normal complement to V in the sense Q=V∨W and W∩V=1;
moreover W centralizes R.

Coprime action gives Q=[Q,T]∨W, hence Q=V∨W. Frattini's argument gives
N(T)Q=G, which becomes N(T)V=G since W≤N(T). Both N(T) and V normalize W:
the first preserves Q and C(T), while the second centralizes Q. Thus W
is ambient normal. Its commutator with R lies in both W and V and vanishes.

This isolates the normality implication used in Stellmacher (4.6), Journal
of Algebra 190 (1997), p26. The statement is ordinary finite group theory
and does not depend on the campaign's residual or module definitions.
-/

namespace Subgroup

/-- The coprime centralizer complement is normal after the Frattini reduction. -/
public theorem coprime_centralizer_normal_complement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (Q V R : Subgroup G) [Q.Normal] [V.Normal]
    (hVQ : V ≤ Q) (hVcent : V ≤ centralizer (Q : Set G))
    (hsolvQ : Group.IsSolvable Q)
    (hcop : Nat.Coprime (Nat.card T) (Nat.card Q))
    (hQT : (Q ⊔ (T : Subgroup G)).Normal)
    (hTR : (T : Subgroup G) ≤ R) (hQR : ⁅Q, R⁆ ≤ V)
    (hfixed : V ⊓ centralizer (T : Set G) = ⊥) :
    let W := Q ⊓ centralizer (T : Set G)
    Q = V ⊔ W ∧ W.Normal ∧ W ≤ centralizer (R : Set G) := by
  let W := Q ⊓ centralizer (T : Set G)
  let N := normalizer (T : Set G)
  have hWQ : W ≤ Q := inf_le_left
  have hWCT : W ≤ centralizer (T : Set G) := inf_le_right
  have hWVbot : W ⊓ V = ⊥ := by
    apply le_bot_iff.mp
    rw [← hfixed]
    exact le_inf inf_le_right (inf_le_left.trans hWCT)
  have hQdecomp : Q = V ⊔ W := by
    have hh := eq_commutator_sup_centralizer_of_solvable_coprime Q (T : Subgroup G)
      le_normalizer_of_normal hsolvQ hcop
    apply le_antisymm
    · rw [hh]
      exact sup_le ((commutator_mono le_rfl hTR).trans hQR |>.trans le_sup_left) le_sup_right
    · exact sup_le hVQ hWQ
  have hWN : W ≤ N := hWCT.trans (centralizer_le_normalizer _)
  have hNnormW : N ≤ normalizer (W : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hWN).mp
    change ((Q.subgroupOf N) ⊓ ((centralizer (T : Set G)).subgroupOf N)).Normal
    infer_instance
  have hVnormW : V ≤ normalizer (W : Set G) :=
    (hVcent.trans (centralizer_le hWQ)).trans (centralizer_le_normalizer _)
  have hNV : N ⊔ V = ⊤ := by
    let _ : (Q ⊔ (T : Subgroup G)).Normal := hQT
    have hh := T.normalizer_sup_eq_top' (le_sup_right : (T : Subgroup G) ≤ Q ⊔ (T : Subgroup G))
    apply top_unique
    rw [← hh, hQdecomp]
    exact sup_le le_sup_left (sup_le
      (sup_le le_sup_right (hWN.trans le_sup_left))
      ((T : Subgroup G).le_normalizer.trans le_sup_left))
  have hWnormal : W.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hNV]
    exact sup_le hNnormW hVnormW
  let _ : W.Normal := hWnormal
  have hWR : ⁅W, R⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hWVbot]
    exact le_inf (commutator_le_left _ _) ((commutator_mono hWQ le_rfl).trans hQR)
  exact ⟨hQdecomp, hWnormal, commutator_eq_bot_iff_le_centralizer.mp hWR⟩

end Subgroup

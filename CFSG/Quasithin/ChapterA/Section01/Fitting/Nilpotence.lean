module

public import Theory.GroupTheory.Fitting.ResidualNilpotence
public import Theory.GroupTheory.PiCore

/-!
# A.1.4: residual centralization forces nilpotence

If K is finite solvable and Oᵖ(K) centralizes Oₚ(K) for every prime dividing
|F(K)|, then K is a π(F(K))-group and K = F(K) is nilpotent. The residual on
the left is superscript Oᵖ, whereas the core on the right is subscript Oₚ.

The reusable Sylow argument proves F(K) = K; equality then identifies the
prime domain and transports nilpotence of the Fitting subgroup to K.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed p.20 (PDF p.31).
-/

public section
namespace CFSG.Quasithin.ChapterA
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A.1.4, with precisely the primes dividing the order of the Fitting subgroup. -/
theorem lemma_A_1_4
    (hsolv : Group.IsSolvable G)
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fittingSubgroup G) →
      pResidual p G ≤ centralizer (pCore p G : Set G)) :
    IsPiGroup {p : Nat.Primes | p.val ∣ Nat.card (fittingSubgroup G)} G ∧
      fittingSubgroup G = ⊤ ∧ Group.IsNilpotent G := by
  have ht := fitting_eq_top_of_pResidual_le_centralizer_pCore hsolv h
  refine ⟨?_, ht, ?_⟩
  · rw [IsPiGroup_iff]
    intro p hp
    change p.val ∣ Nat.card (fittingSubgroup G)
    simpa only [ht, card_top] using hp
  · exact Group.nilpotent_of_mulEquiv
      ((MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv)

end CFSG.Quasithin.ChapterA

module

public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.Restriction

/-!
# Unique conjugate normalizer for an irreducible radical actor

If X is two-perfect with an elementary or extraspecial odd quotient and
N_G(X)=M is strongly quasithin, any irreducible actor X ≤ S ≤ M lies in
only one conjugate of M. The local comparison gives X ≤ Xᵍ; finite order
makes this equality, so the original conjugating element lies in M.

Source: Aschbacher--Smith 13.1.11, printed p.872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity
open Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- Full conjugate rigidity, including membership of the original conjugator. -/
theorem conjugate_eq_of_irreducible {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (X M S : Subgroup G) (hM : IsStronglyQuasithin M)
    (hNX : normalizer (X : Set G) = M)
    (hX : IsPPerfect 2 X) (hqX : XiOddQuotient p (XiQuotient X))
    (hXS : X ≤ S) (hSM : S ≤ M)
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : S, ∀ a ∈ A, xiFrattiniAction S X (hSM.trans hNX.ge) s a ∈ A) →
        A = ⊥ ∨ A = ⊤)
    (g : G) (hSg : S ≤ M.conjBy g) : g ∈ M ∧ M.conjBy g = M := by
  let e : X ≃* X.conjBy g := (MulAut.conj g).subgroupMap X
  let eM : M ≃* M.conjBy g := (MulAut.conj g).subgroupMap M
  have hXM : X ≤ M := X.le_normalizer.trans_eq hNX
  have hYM : X.conjBy g ≤ M.conjBy g := map_mono hXM
  have hNY : normalizer (X.conjBy g : Set G) = M.conjBy g := by
    change normalizer (X.map (MulAut.conj g).toMonoidHom : Set G) =
      M.map (MulAut.conj g).toMonoidHom
    rw [← map_equiv_normalizer_eq, hNX]
  have hYn : ((X.conjBy g).subgroupOf (M.conjBy g)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYM).mpr hNY.ge
  have hMg : IsStronglyQuasithin (M.conjBy g) := by
    intro r hr hor
    rw [← primeRank_congr r eM]
    exact hM r hr hor
  have hqY : XiOddQuotient p (XiQuotient (X.conjBy g)) :=
    hqX.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hle : X ≤ X.conjBy g := le_normal_radical_in ho (M.conjBy g) X (X.conjBy g) S
    hMg (hXS.trans hSg) hYM hSg hYn hX hqX hqY hXS (hSM.trans hNX.ge) hirr
  have he : X = X.conjBy g := eq_of_le_of_card_ge hle (Nat.card_congr e.toEquiv).symm.le
  have hg : g ∈ M := hNX ▸ mem_normalizer_iff_map_conj_eq.mpr he.symm
  exact ⟨hg, mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hg)⟩

end CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity

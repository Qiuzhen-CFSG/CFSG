module

public import CFSG.Quasithin.ChapterA.Section01.Fitting.Product.Components
public import Theory.GroupTheory.GeneralizedFitting.OddNormalObstruction
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Characteristic two in a normal product

We prove the literal characteristic-two conclusion F*(G) = O₂(G) for
G = LM with L normal, retaining the intrinsic hypotheses on L and M,
the ambient Sylow subgroup in M, and Q ≤ O₂(M) with N_G(Q) ≤ M.

The component case is proved in `Product.Components`. For an odd prime p,
the normal subgroup X = Oₚ(G) meets L trivially. The equivariant projection
from LX onto X is surjective on M ∩ LX. Its image of O₂(M) ∩ LX is trivial,
forcing X to centralize O₂(M) and thus Q. The normalizer hypothesis puts
X in M, whose characteristic-two hypothesis forces X = 1. The prime-core
decomposition of the Fitting subgroup now completes the theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.1.10, printed p.21 (PDF p.32).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.FittingProduct
variable {G : Type*} [Group G] [Finite G]

/-- The normal odd-prime subgroup case of A.1.10, with the actual embedded
two-core of M and the supplied normalizer bound. -/
private theorem odd_normal_eq_bot (L M Q : Subgroup G) [L.Normal]
    (hgen : L ⊔ M = ⊤)
    (hL : generalizedFitting L = pCore 2 L)
    (hM : generalizedFitting M = pCore 2 M)
    (hQ : Q ≤ (pCore 2 M).map M.subtype) (hNQ : normalizer (Q : Set G) ≤ M)
    (p : ℕ) [Fact p.Prime] (hp : 2 ≠ p)
    (X : Subgroup G) [X.Normal] (hX : IsPGroup p X) : X = ⊥ := by
  have hXL : X.subgroupOf L = ⊥ :=
    normal_pGroup_eq_bot_of_generalizedFitting_eq_pCore hp hL _ hX.comap_subtype
  have hd : Disjoint L X := (subgroupOf_eq_bot.mp hXL).symm
  let P := (pCore 2 M).map M.subtype
  have hn : M ≤ normalizer (P : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hc : P ≤ centralizer (X : Set G) :=
    centralizes_coprime_normal_factor_of_product L M X P hgen hd
      (pCore_isPGroup.map M.subtype) hX
      ((Nat.coprime_primes (by decide) (Fact.out : p.Prime)).mpr hp) hn
  have hXM : X ≤ M :=
    ((le_centralizer_iff.mp hc).trans (centralizer_le hQ)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNQ)
  have hXMb : X.subgroupOf M = ⊥ :=
    normal_pGroup_eq_bot_of_generalizedFitting_eq_pCore hp hM _ hX.comap_subtype
  exact (subgroupOf_eq_bot.mp hXMb).eq_bot_of_le hXM

end FittingProduct

/-- A.1.10: a normal product of characteristic-two groups has characteristic two
when its supplement contains a Sylow two-subgroup and controls the normalizer
of a subgroup of its own two-core. -/
theorem lemma_A_1_10 {G : Type*} [Group G] [Finite G]
    (L M : Subgroup G) [L.Normal] (hgen : L ⊔ M = ⊤)
    (hL : generalizedFitting L = pCore 2 L)
    (hM : generalizedFitting M = pCore 2 M)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (Q : Subgroup G) (hQ : Q ≤ (pCore 2 M).map M.subtype)
    (hNQ : normalizer (Q : Set G) ≤ M) :
    generalizedFitting G = pCore 2 G := by
  have hE : componentLayer G = ⊥ := by
    apply sSup_eq_bot.mpr
    intro X hX
    exact (FittingProduct.no_component L M hgen hL hM T hTM X hX).elim
  have hF : fittingSubgroup G ≤ pCore 2 G := by
    rw [fitting_eq_sup_pCore]
    apply iSup_le
    intro p
    let : Fact p.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.val.property⟩
    by_cases hp : 2 = p.val.val
    · rw [← hp]
    · rw [FittingProduct.odd_normal_eq_bot L M Q hgen hL hM hQ hNQ
        p.val.val hp (pCore p.val.val G) pCore_isPGroup]
      exact bot_le
  apply le_antisymm
  · simpa only [generalizedFitting, hE, sup_bot_eq] using hF
  · exact (pCore_le_fitting G 2).trans (fitting_le_generalizedFitting G)
end CFSG.Quasithin.ChapterA

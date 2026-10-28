module
public import Stellmacher.BaumannTwoOvergroupNormalizer
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Baumann commutators normalize a Sylow/core intersection

Let S be a Sylow two-subgroup, B its elementary Baumann subgroup, and
K satisfies K=[K,B], while R is either normalized by S or satisfies
R=[R,B]. Suppose the two-subgroup Q is
normalized by R, K, and B, while O2(R) and O2(K) lie in S. Then
R join K join B normalizes S intersect Q.

The Baumann weak-closure theorem shows Q normalizes B. Full-commutator
normalizer transfer then shows Q normalizes K. The commutator
[R,S intersect Q] lies in R because S normalizes R (or because the
full-commutator argument makes Q normalize R). It also lies in Q, and
R intersect Q is a normal two-subgroup of R, hence lies in O2(R).
The same argument for K bounds its commutator with S intersect Q.
Both commutators thus lie in S intersect Q,
which proves the asserted normalization; B normalizes both S and Q.

This replaces the common-Sylow argument in the repeated transfer of
Stellmacher (6.4), Journal of Algebra 190 (1997), p.32. There Q is the
core of a local join involving O^2(P1) and O^2(F2). The generators need
not have a common Sylow subgroup. The first-generator Sylow normalization or full Baumann commutator,
the second-generator full commutator, and the ambient Sylow S remain explicit.
Source: refs/files/stellmacher-n-group.pdf, final paragraph of (6.4),
and the normalizer argument in (5.2).
-/

namespace Stellmacher

private theorem pCore_le_of_normal_inf
    {H : Type*} [Group H] [Finite H]
    (R Q S : Subgroup H) (hQp : IsPGroup 2 Q)
    (hRN : R ≤ Subgroup.normalizer (Q : Set H))
    (hQN : S ⊓ Q ≤ Subgroup.normalizer (R : Set H))
    (hcore : twoCoreAmbient R ≤ S) :
    R ≤ Subgroup.normalizer ((S ⊓ Q : Subgroup H) : Set H) := by
  let D := R ⊓ Q
  have hDR : D ≤ R := inf_le_left
  have hDn : (D.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDR).mpr
      ((le_inf R.le_normalizer hRN).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have hDp : IsPGroup 2 (D.subgroupOf R) :=
    (hQp.to_le (show D ≤ Q from inf_le_right)).comap_of_injective
      R.subtype R.subtype_injective
  have hDcore : D ≤ twoCoreAmbient R := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hDR]
    exact Subgroup.map_mono (le_sSup ⟨hDn, hDp⟩)
  have hRQ : ⁅R,S ⊓ Q⁆ ≤ D := le_inf
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hQN)
    ((Subgroup.commutator_mono le_rfl inf_le_right).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hRN))
  exact Subgroup.le_normalizer_iff_commutator_le_right.mpr
    (le_inf (hRQ.trans (hDcore.trans hcore)) (hRQ.trans inf_le_right))

private theorem global_full_commutator_normalizer
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (R Q : Subgroup H) (hQp : IsPGroup 2 Q)
    (hnorm : R ⊔ ((S : Subgroup H) ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) : Set H)) ≤ Subgroup.normalizer (Q : Set H))
    (hRB : R = ⁅R,((S : Subgroup H) ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) : Set H))⁆) :
    Q ≤ Subgroup.normalizer (R : Set H) := by
  let B := ((S : Subgroup H) ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) : Set H))
  have hBp : IsPGroup 2 B := S.isPGroup'.to_le inf_le_left
  have hBQ : B ≤ Subgroup.normalizer (Q : Set H) := le_sup_right.trans hnorm
  have hQBp : IsPGroup 2 (Q ⊔ B : Subgroup H) := hQp.to_sup_of_normal_left' hBp hBQ
  have hQB : Q ≤ Subgroup.normalizer (B : Set H) := by
    apply le_sup_left.trans
    simpa only [B] using
      (twoSubgroup_le_normalizer_baumann S (Q ⊔ B) hQBp le_sup_right)
  exact Subgroup.twoSubgroup_le_normalizer_of_full_commutator R B Q hBp hQp
    hnorm hQB hRB.symm

public theorem full_baumann_commutators_normalize_core_intersection
    {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (R K Q : Subgroup H) :
    let B := (S : Subgroup H) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) : Set H)
    IsPGroup 2 Q →
    R ⊔ B ≤ Subgroup.normalizer (Q : Set H) →
    K ⊔ B ≤ Subgroup.normalizer (Q : Set H) →
    R = ⁅R, B⁆ → K = ⁅K, B⁆ →
    twoCoreAmbient R ≤ (S : Subgroup H) →
    twoCoreAmbient K ≤ (S : Subgroup H) →
    R ⊔ K ⊔ B ≤
      Subgroup.normalizer (((S : Subgroup H) ⊓ Q : Subgroup H) : Set H) := by
  dsimp only
  intro hQp hRQ hKQ hRB hKB hRc hKc
  have hQR := global_full_commutator_normalizer S R Q hQp hRQ hRB
  have hQK := global_full_commutator_normalizer S K Q hQp hKQ hKB
  refine sup_le (sup_le ?_ ?_) ?_
  · exact pCore_le_of_normal_inf R Q (S : Subgroup H) hQp
      (le_sup_left.trans hRQ) (inf_le_right.trans hQR) hRc
  · exact pCore_le_of_normal_inf K Q (S : Subgroup H) hQp
      (le_sup_left.trans hKQ) (inf_le_right.trans hQK) hKc
  · exact (le_inf ((show ((S : Subgroup H) ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) : Set H)) ≤ (S : Subgroup H) from inf_le_left).trans
      (S : Subgroup H).le_normalizer) (le_sup_right.trans hRQ)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
/-- The first generator may instead be normalized by the original Sylow. -/
public theorem baumann_pair_normalizes_core_intersection
    {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (R K Q : Subgroup H) :
    let B := (S : Subgroup H) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H)) : Set H)
    IsPGroup 2 Q →
    R ⊔ B ≤ Subgroup.normalizer (Q : Set H) →
    K ⊔ B ≤ Subgroup.normalizer (Q : Set H) →
    (S : Subgroup H) ≤ Subgroup.normalizer (R : Set H) → K = ⁅K, B⁆ →
    twoCoreAmbient R ≤ (S : Subgroup H) →
    twoCoreAmbient K ≤ (S : Subgroup H) →
    R ⊔ K ⊔ B ≤
      Subgroup.normalizer (((S : Subgroup H) ⊓ Q : Subgroup H) : Set H) := by
  dsimp only
  intro hQp hRQ hKQ hSR hKB hRc hKc
  have hQK := global_full_commutator_normalizer S K Q hQp hKQ hKB
  refine sup_le (sup_le ?_ ?_) ?_
  · exact pCore_le_of_normal_inf R Q (S : Subgroup H) hQp
      (le_sup_left.trans hRQ) (inf_le_left.trans hSR) hRc
  · exact pCore_le_of_normal_inf K Q (S : Subgroup H) hQp
      (le_sup_left.trans hKQ) (inf_le_right.trans hQK) hKc
  · exact (le_inf (inf_le_left.trans (S : Subgroup H).le_normalizer)
      (le_sup_right.trans hRQ)).trans Subgroup.inf_normalizer_le_normalizer_inf
end Stellmacher

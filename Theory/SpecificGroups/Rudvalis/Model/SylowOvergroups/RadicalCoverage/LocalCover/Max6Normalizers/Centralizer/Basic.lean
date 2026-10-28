module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Words
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Refinement

/-!
# Centralizer-invariant colors for the fixed max6 involution

A commuting permutation preserves fixed points of the involution, adjacency
between a point and its involution image, and colors obtained by counting
neighbors in invariant cells. Individualizing fixed points also individualizes
their involution images. These facts support a three-point stabilizer argument.

Source: the preserved ATLAS RuG1-max6W1 words and degree-4060 orbital, as
attributed in SylowOvergroups.Definitions and OuterNormalizer.Invariance;
GLS3 Table 5.3r and [Asc86b], cited on quasithin printed p.511.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.CentralizerCertificate
open Rudvalis.OuterNormalizer
open Rudvalis.OuterNormalizer.InvarianceCertificate
open Rudvalis.OuterNormalizer.RigidityCertificate

@[expose] public def baseColor (x : Fin 4060) : Nat :=
  if AlignmentData.involutionPerm x = x then 0
  else if cachedAdj x (AlignmentData.involutionPerm x) then 2 else 1

public theorem baseColor_preserved (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut)
    (hz : ∀ x, p (AlignmentData.involutionPerm x) = AlignmentData.involutionPerm (p x))
    (x : Fin 4060) : baseColor (p x) = baseColor x := by
  have hf : AlignmentData.involutionPerm (p x) = p x ↔
      AlignmentData.involutionPerm x = x := by
    rw [← hz]
    exact p.injective.eq_iff
  have ha : cachedAdj (p x) (AlignmentData.involutionPerm (p x)) ↔
      cachedAdj x (AlignmentData.involutionPerm x) := by
    rw [← hz]
    exact (cachedAdj_iff_adj _ _).trans ((hp _ _).trans (cachedAdj_iff_adj _ _).symm)
  simp only [baseColor, hf, ha]

@[expose] public def seed (k : Nat) (x : Fin 4060) : Nat :=
  (baseColor x * (k + 1) + initial k x) * (k + 1) +
    initial k (AlignmentData.involutionPerm x)

public theorem seed_preserved (k : Nat) (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut)
    (hz : ∀ x, p (AlignmentData.involutionPerm x) = AlignmentData.involutionPerm (p x))
    (hf : ∀ x : Fin 4060, x.val < k → p x = x) :
    ∀ x, seed k (p x) = seed k x := by
  intro x
  simp only [seed, baseColor_preserved p hp hz, ← hz, initial_preserved k p hf]

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.CentralizerCertificate

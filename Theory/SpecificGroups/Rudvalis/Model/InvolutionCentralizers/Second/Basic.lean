module
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Refinement
public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase

/-!
# Invariant colors for the second Rudvalis involution centralizer

A permutation commuting with the literal ATLAS generator a preserves its
fixed points and adjacency between x and a(x) in the certified orbital.
Individualized points and their a-images give the seeds for a two-point
stabilizer calculation. These lemmas make no centralizer-shape assumption.

Source: ATLAS RuG1-p4060B0, with inverse-action conventions in
Model.PermutationData; GLS3 Table 5.3r and Quasithin 16.1.5(11).
-/

public section
namespace Rudvalis.InvolutionCentralizers.SecondCertificate
open OuterNormalizer OuterNormalizer.InvarianceCertificate OuterNormalizer.RigidityCertificate

@[expose] def baseColor (x : Fin 4060) : Nat :=
  if aPerm x = x then 0 else if cachedAdj x (aPerm x) then 2 else 1

theorem baseColor_preserved (p : Equiv.Perm (Fin 4060)) (hp : p ∈ relationAut)
    (ha : ∀ x, p (aPerm x) = aPerm (p x)) (x : Fin 4060) :
    baseColor (p x) = baseColor x := by
  have hf : aPerm (p x) = p x ↔ aPerm x = x := by
    rw [←ha]
    exact p.injective.eq_iff
  have he : cachedAdj (p x) (aPerm (p x)) ↔ cachedAdj x (aPerm x) := by
    rw [←ha]
    exact (cachedAdj_iff_adj _ _).trans ((hp _ _).trans (cachedAdj_iff_adj _ _).symm)
  simp only [baseColor,hf,he]

@[expose] def seed (k : Nat) (x : Fin 4060) : Nat :=
  (baseColor x * (k+1) + initial k x) * (k+1) + initial k (aPerm x)

theorem seed_preserved (k : Nat) (p : Equiv.Perm (Fin 4060)) (hp : p ∈ relationAut)
    (ha : ∀ x, p (aPerm x) = aPerm (p x))
    (hf : ∀ x : Fin 4060, x.val < k → p x = x) :
    ∀ x, seed k (p x) = seed k x := by
  intro x
  simp only [seed,baseColor_preserved p hp ha,←ha,initial_preserved k p hf]

end Rudvalis.InvolutionCentralizers.SecondCertificate

module

public import CFSG.Quasithin.ChapterA.Section03.RankThreeSylow
public import CFSG.Quasithin.ChapterA.Section03.RankThreeAutomizers
public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Basic

/-!
# Concrete rank-three local matrix calculations

For every odd prime p, this module assembles the three local properties used
in the proof of A.3.21 for the actual SL₃(p) and SU₃(p). Each group has one
nonempty involution class, whose centralizer has prime-to-p residual SL₂(p)
containing its terminal derived subgroup. Every Sylow two-subgroup is
semidihedral or wreathed, has elementary abelian two-rank exactly two, and
has cyclic center. Every odd cross-characteristic prime-subgroup has the
abelian S₃-automizer alternative or the exceptional solvable three-automizer
alternative, with the appropriate congruence on p.

The proofs combine the concrete conjugacy and centralizer calculations,
the Sylow presentations transported through the odd-index centralizers,
and the faithful degree-three representation arguments. The linear model
uses ZMod p; the unitary model uses GF(p²), identity Gram matrix and
conjugation x ↦ x^p. The imported APIs retain the full GL₂(p) and GU₂(p)
centralizer isomorphisms and the explicit field witnesses. The original
standard linear involution API is preserved below.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Lemma
A.3.21, printed pp. 55–56 (PDF pp. 66–67).
-/

public section

namespace CFSG.Quasithin.ChapterA.Section03

private theorem primeField_two_ne_zero (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (2 : ZMod p) ≠ 0 := by
  apply CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two
  obtain ⟨k, hk⟩ := hp
  omega

/-- The chosen linear matrix is an involution for every odd prime. -/
theorem sl3_standard_involution_order (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    orderOf (Matrix.SL3.standardInvolution (ZMod p)) = 2 :=
  Matrix.SL3.standardInvolution_orderOf (ZMod p) (primeField_two_ne_zero p hp)

/-- The standard involution centralizer over the prime field is the actual GL₂. -/
noncomputable def sl3_standard_involution_centralizer (p : ℕ) [Fact p.Prime]
    (hp : Odd p) :
    Subgroup.centralizer ({Matrix.SL3.standardInvolution (ZMod p)} :
      Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) ≃* GL (Fin 2) (ZMod p) :=
  (Matrix.SL3.standardInvolutionCentralizerEquiv (ZMod p)
    (primeField_two_ne_zero p hp)).symm

/-- The local properties (a)–(c) used in the proof of A.3.21, together with
the cyclic Sylow center used immediately afterwards. The parameter `residue`
is the representative modulo three of the source sign ε: one for SL₃ and
two for SU₃. The two-rank clause gives both a four-subgroup and the bound
on all elementary abelian two-subgroups. -/
structure RankThreeLocalStructure (L : Type*) [Group L] (p residue : ℕ) : Prop where
  /-- One nonempty involution class and the actual SL₂(p) centralizer residual. -/
  involutions : ∃ z : L, orderOf z = 2 ∧
    ∀ w : L, orderOf w = 2 → IsConj z w ∧
      Nonempty (Subgroup.primeToResidual p (Subgroup.centralizer ({w} : Set L)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ∧
      (⨅ n : ℕ, derivedSeries (Subgroup.centralizer ({w} : Set L)) n) ≤
        Subgroup.primeToResidual p (Subgroup.centralizer ({w} : Set L))
  /-- Genuine Sylow presentations, exact elementary two-rank, and cyclic center. -/
  sylow : ∀ T : Sylow 2 L,
    (Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T) ∧
    (∃ E : Subgroup T, IsElementaryAbelian 2 E ∧ Nat.card E = 4) ∧
    (∀ E : Subgroup T, IsElementaryAbelian 2 E → Nat.card E ≤ 4) ∧
    IsCyclic (Subgroup.center T)
  /-- The automizer is the image of conjugation by the actual normalizer. -/
  automizers : ∀ (q : ℕ) [Fact q.Prime], Odd q → q ≠ p →
    ∀ Q : Subgroup L, IsPGroup q Q →
      (IsMulCommutative Q ∧
        ∃ j : Q.normalizerMonoidHom.range →* Equiv.Perm (Fin 3), Function.Injective j) ∨
      (q = 3 ∧ p % 3 = residue ∧ Group.IsSolvable Q.normalizerMonoidHom.range)

/-- All three local properties used in A.3.21 for SL₃ over the prime field,
with every premise discharged from the odd-prime hypothesis. -/
theorem sl3_local_structure (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    RankThreeLocalStructure (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) p 1 := by
  refine ⟨sl3_involution_structure p hp, sl3_sylow_structure p hp, ?_⟩
  intro q hqprime hq hqp Q hQ
  exact sl3_odd_subgroup_automizer p q hp hq hqp Q hQ

/-- All three local properties used in A.3.21 for the actual SU₃ over GF(p²)
with p-power conjugation. The exceptional congruence is p ≡ -1 modulo three. -/
theorem su3_local_structure (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    RankThreeLocalStructure (RankThreeSU p) p 2 := by
  refine ⟨su3_involution_structure p hp, su3_sylow_structure p hp, ?_⟩
  intro q hqprime hq hqp Q hQ
  exact su3_odd_subgroup_automizer p q hp hq hqp Q hQ

end CFSG.Quasithin.ChapterA.Section03

end

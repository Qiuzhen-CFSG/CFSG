module

public import CFSG.Quasithin.ChapterG.Section08.Defs
public import Theory.GroupTheory.Commutator.NilpotentAB
public import Theory.GroupTheory.NilpotentComplementCentralizers
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The nilpotent faithful-centralizer step in G.8

The local two-core calculation in G.8.3 is proved for normal nilpotent
two-complements. The coprime nilpotent A × B lemma identifies the kernels on X and C_X(Y)
when the actor centralizes Y. For a two-group acting on an odd-order group,
the orders are coprime, giving G.8.4 without any extra hypothesis.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, G.8.3–4,
printed p.349, combined manuscript of 1 March 2004.
-/

namespace CFSG.Quasithin.ChapterG.Section08

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- G.8.3. Both cores are compared inside the ambient group. The normal
odd-order X and two-group complement P realize the source semidirect product. -/
public theorem lemma_G_8_3 (X P U : Subgroup G) [X.Normal]
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hP : IsPGroup 2 P) (hgen : X ⊔ P = ⊤) (hUX : U ≤ X) :
    (centralizer (U : Set G)).pCoreIn 2 = pCore 2 G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact pCoreIn_centralizer_eq_of_nilpotent_normal_complement 2 X U hX
    hodd.coprime_two_left (isPGroup_quotient_of_sup_eq_top X P hP hgen) hUX

/-- G.8.4 in the ambient-subgroup formulation. Normalization and
faithfulness refer to the actual conjugation action. -/
public theorem lemma_G_8_4 (P X Y : Subgroup G)
    (hP : IsPGroup 2 P) (hX : Group.IsNilpotent X)
    (hodd : Odd (Nat.card X)) (hYX : Y ≤ X)
    (hnorm : P ≤ normalizer (X : Set G))
    (hcent : P ≤ centralizer (Y : Set G))
    (hfaith : P ⊓ centralizer (X : Set G) = ⊥) :
    P ⊓ centralizer (X ⊓ centralizer (Y : Set G) : Set G) = ⊥ := by
  have hcop : Nat.Coprime (Nat.card P) (Nat.card X) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    exact hodd.coprime_two_left.pow_left k
  rw [nilpotent_centralizer_restriction_kernel X Y P hX hYX hnorm hcent hcop]
  exact hfaith

end CFSG.Quasithin.ChapterG.Section08

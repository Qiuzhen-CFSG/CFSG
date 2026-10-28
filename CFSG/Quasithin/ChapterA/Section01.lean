module

public import Theory.ThreeSubgroups
public import Theory.GroupTheory.BaerSuzukiSubgroup
public import Theory.GroupTheory.Involution.OddRotation
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.CyclicSylowNormalComplement

/-!
# Elementary group theory for the quasithin classification

This module assembles §A.1 of Aschbacher–Smith, *The Classification of
Quasithin Groups* (1 March 2004 manuscript). The basic commutator, p-core,
quotient intersection and normal-complement results are supplied by reusable
group theory modules. Further parts of the section will be assembled from
its separate prerequisite modules.
-/

namespace CFSG.Quasithin.ChapterA

variable {G : Type*} [Group G]

/-- A.1.1, the three-subgroup lemma. -/
public theorem lemma_A_1_1 (X Y Z : Subgroup G)
    (hXY : ⁅⁅X, Y⁆, Z⁆ = ⊥) (hYZ : ⁅⁅Y, Z⁆, X⁆ = ⊥) :
    ⁅⁅Z, X⁆, Y⁆ = ⊥ :=
  Subgroup.commutator_commutator_eq_bot_of_rotate hXY hYZ

/-- A.1.2, the subgroup form of Baer–Suzuki. -/
public theorem lemma_A_1_2 [Finite G] {p : ℕ} [Fact p.Prime]
    (X : Subgroup G) (hX : IsPGroup p X) :
    X ≤ pCore p G ∨
      ∃ g : G, ¬ IsPGroup p (X ⊔ X.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
  X.le_pCore_or_exists_conjugate_sup_not_isPGroup hX

/-- A.1.2, the nontrivial odd-order inversion consequence in the branch
outside the two-core. -/
public theorem lemma_A_1_2_involution [Finite G]
    (t : G) (ht : BenderSuzuki.PFAppendixIII.IsInvolution t) (htcore : t ∉ pCore 2 G) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      ∃ r : G, orderOf r = q ∧ t⁻¹ * r * t = r⁻¹ :=
  BenderSuzuki.involution_outside_twoCore_inverts_odd_prime t ht htcore

/-- A.1.6, containment of the two-core in a Sylow overgroup. -/
public theorem lemma_A_1_6_core [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) :
    pCore 2 G ≤ (pCore 2 H).map H.subtype :=
  Subgroup.pCore_le_map_of_sylow_le T H hTH

/-- A.1.6, preservation of the self-centralizing two-core formulation. -/
public theorem lemma_A_1_6_centralizer [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hG : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    Subgroup.centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
  Subgroup.centralizer_pCore_le_of_sylow_le T H hTH hG

/-- A.1.16(1), the quotient image of an intersection. -/
public theorem lemma_A_1_16_1 (Y C D : Subgroup G) [Y.Normal] (hYD : Y ≤ D) :
    (C ⊓ D).map (QuotientGroup.mk' Y) =
      C.map (QuotientGroup.mk' Y) ⊓ D.map (QuotientGroup.mk' Y) := by
  apply Subgroup.map_inf_of_ker_le
  simpa only [QuotientGroup.ker_mk'] using hYD

/-- A.1.38, a cyclic Sylow subgroup at the least prime has a normal complement. -/
public theorem lemma_A_1_38 [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp : (Nat.card G).minFac = p) (hP : IsCyclic P) :
    HasNormalPComplement p G :=
  BenderSuzuki.External.Suzuki.V.suzuki_ch5_theorem_2_10_corollary_1 P hp hP

end CFSG.Quasithin.ChapterA

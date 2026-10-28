module

public import CFSG.Quasithin.ChapterG.Section08
public import CFSG.Quasithin.ChapterG.Section08.DihedralProducts.G09Extraction
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!+# Applications of the complete dihedral and Θ-faithfulness theorems

The four extraction clauses in the fifth observation of G.9.2 are now
unconditional: the proved G.8.2 discharges their faithful-complement input.
The specialization to `NilpotentRigidity.Hypothesis` uses the original actor,
nilpotent subgroup and residuals.

For A.4.4, the two quotient applications retain the literal map
H → H/O₂(H). A two-subgroup whose image centralizes the specified subgroup
lies in O₂(H), by G.8.9. The preceding centralization step is the separate
A.4.2.3 input, owned by the A.4 assembly; it is explicit here. These are
applications of G.8.9, not assertions of the remaining A.4.4 conclusions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
printed pp.58 and 352, combined manuscript of 1 March 2004.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section08

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- The complete G.8 group-theoretic extraction input to G.9.2. -/
theorem dihedralExtraction (A X : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (n : ℕ) (hcard : Nat.card A = 2 ^ n) :
    CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralExtraction A X n :=
  dihedralExtraction_of_faithfulComplement (faithfulComplementTheorem G)
    A X hA hX hodd hnorm hfaith n hcard

/-- A.4.4(a)'s final quotient step: G.8.9(2) kills the actual image of
the two-subgroup, placing it in the original two-core. -/
theorem le_twoCore_of_theta_quotient_centralizes
    (U : Subgroup G) (hU : IsPGroup 2 U)
    (θ : Subgroup (G ⧸ pCore 2 G)) (hθ : IsThetaSubgroup θ)
    (hc : U.map (QuotientGroup.mk' (pCore 2 G)) ≤ centralizer (θ : Set (G ⧸ pCore 2 G))) :
    U ≤ pCore 2 G := by
  have hf := lemma_G_8_9_2 (pCore_quotient_pCore_eq_bot 2) hθ
    (U.map (QuotientGroup.mk' (pCore 2 G))) (hU.map _)
  have hz : U.map (QuotientGroup.mk' (pCore 2 G)) = ⊥ := by
    rw [inf_eq_left.mpr hc] at hf
    exact hf
  simpa only [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hz

/-- A.4.4(b)'s final quotient step, preserving relative subnormality and
the prime-order centralizer hypothesis inside the actual quotient F*. -/
theorem le_twoCore_of_prime_centralizer_quotient_centralizes
    (U : Subgroup G) (hU : IsPGroup 2 U)
    (X : Subgroup (G ⧸ pCore 2 G))
    (hXF : X ≤ generalizedFitting (G ⧸ pCore 2 G))
    (hsub : (X.subgroupOf (generalizedFitting (G ⧸ pCore 2 G))).IsSubnormal)
    (hprime : primeOrderGenerated
      (generalizedFitting (G ⧸ pCore 2 G) ⊓ centralizer (X : Set (G ⧸ pCore 2 G))) ≤ X)
    (hc : U.map (QuotientGroup.mk' (pCore 2 G)) ≤ centralizer (X : Set (G ⧸ pCore 2 G))) :
    U ≤ pCore 2 G := by
  have hf := lemma_G_8_9_1 (pCore_quotient_pCore_eq_bot 2) X
    (U.map (QuotientGroup.mk' (pCore 2 G))) hXF hsub hprime (hU.map _)
    (hc.trans (Subgroup.centralizer_le_normalizer _))
  have hz : U.map (QuotientGroup.mk' (pCore 2 G)) = ⊥ := by
    rw [inf_eq_left.mpr hc] at hf
    exact hf
  simpa only [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hz

end CFSG.Quasithin.ChapterG.Section08

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

/-- The actual G.9.2 hypotheses now supply all four extraction clauses
without an extra complement or dihedral-existence premise. -/
theorem Hypothesis.dihedralExtraction
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    {A X : Subgroup G} {n : ℕ} (h : Hypothesis ρ A X n) :
    DihedralExtraction A X n :=
  h.dihedralExtraction_of_faithfulComplement
    (CFSG.Quasithin.ChapterG.Section08.faithfulComplementTheorem G)

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

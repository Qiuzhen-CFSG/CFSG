module

public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.PCoreCentralQuotient

/-!
# Characteristic p and the generalized Fitting subgroup

The intrinsic equality `F*(G) = O_p(G)` is equivalent to self-centralization
of the p-core. Generalized-Fitting self-centralization gives one direction;
the component calculus excludes the layer and the other prime cores for the
converse. We then transfer the equality to Sylow overgroups and central
quotients using the corresponding p-core theorems.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, the
observation preceding A.1.1 and Lemmas A.1.6 and A.1.8, printed pp.20–21.
The Chapter B import supplies the audited bridge from the intrinsic definition
to the Gorenstein–Walter generalized-Fitting self-centralization theorem.
-/

public section
namespace CFSG.Quasithin.ChapterA
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The generalized-Fitting and self-centralizing-core definitions of
characteristic p agree. -/
theorem generalizedFitting_eq_pCore_iff (p : ℕ) [Fact p.Prime] :
    generalizedFitting G = pCore p G ↔
      centralizer (pCore p G : Set G) ≤ pCore p G := by
  constructor
  · intro h
    rw [← h]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  · exact generalizedFitting_eq_pCore_of_selfCentralizing p

/-- A.1.6: both the p-core containment and the generalized-Fitting equality
pass to an overgroup of a Sylow subgroup (stated in the source for p = 2). -/
theorem lemma_A_1_6_general (p : ℕ) [Fact p.Prime] (T : Sylow p G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hG : generalizedFitting G = pCore p G) :
    pCore p G ≤ (pCore p H).map H.subtype ∧ generalizedFitting H = pCore p H :=
  ⟨pCore_le_map_of_sylow_le T H hTH,
    (generalizedFitting_eq_pCore_iff p).mpr
      (centralizer_pCore_le_of_sylow_le T H hTH
        ((generalizedFitting_eq_pCore_iff p).mp hG))⟩

/-- A.1.6 in its printed characteristic-two formulation. -/
theorem lemma_A_1_6 (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hG : generalizedFitting G = pCore 2 G) :
    pCore 2 G ≤ (pCore 2 H).map H.subtype ∧ generalizedFitting H = pCore 2 H :=
  lemma_A_1_6_general 2 T H hTH hG

/-- A.1.8: characteristic p is preserved by a quotient with central kernel. -/
theorem lemma_A_1_8 (p : ℕ) [Fact p.Prime]
    (hG : generalizedFitting G = pCore p G) (X : Subgroup G) [X.Normal]
    (hX : X ≤ center G) : generalizedFitting (G ⧸ X) = pCore p (G ⧸ X) := by
  apply (generalizedFitting_eq_pCore_iff p).mpr
  apply MonoidHom.centralizer_pCore_le_of_surjective_centralKernel
    (QuotientGroup.mk' X) (QuotientGroup.mk'_surjective X)
  · simpa only [QuotientGroup.ker_mk'] using hX
  · exact (generalizedFitting_eq_pCore_iff p).mp hG

end CFSG.Quasithin.ChapterA

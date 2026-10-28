module
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
/-!
# Characteristic p for subgroups normalized by the ambient prime core

If F*(G)=O_p(G) and O_p(G) normalizes I, pass through I O_p(G).
This overgroup of the ambient prime core has characteristic p, and I is
normal in it. Normal-subgroup inheritance gives F*(I)=O_p(I).

This is the generalized-Fitting step of Aschbacher–Smith E.2.9(2); it needs
neither solvability nor a model for the quotient of I.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem generalizedFitting_eq_pCore_of_normalized_by_pCore (I : Subgroup G)
    (hc : generalizedFitting G = pCore p G)
    (hn : pCore p G ≤ normalizer (I : Set G)) :
    generalizedFitting I = pCore p I := by
  have hself : centralizer (pCore p G : Set G) ≤ pCore p G := by
    rw [← hc]
    exact centralizer_generalizedFitting_le G
  let H := I ⊔ pCore p G
  have hH : centralizer (pCore p H : Set H) ≤ pCore p H :=
    centralizer_pCore_le_of_pCore_le H hself le_sup_right
  let : (I.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le I.le_normalizer hn)
  have hI := normal_core_selfCentralizing hH (I.subgroupOf H)
  exact generalizedFitting_eq_pCore_of_selfCentralizing p
    ((Theory.Quasithin.centralizer_pCore_le_iff p
      (subgroupOfEquivOfLe (show I ≤ H from le_sup_left))).mp hI)
end Theory.GroupTheory

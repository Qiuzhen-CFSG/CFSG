module

public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Characteristic p from a p-group centralizer

If a p-subgroup Q has p-group centralizer, its normalizer has characteristic p.
Inside the normalizer, both Q and its centralizer are normal p-subgroups and
therefore lie in the p-core. The centralizer of that core centralizes Q and
hence lies in the core as well. The generalized-Fitting characterization then
applies.

This standard local argument is used in the sporadic inspection of
Aschbacher--Smith, 15.3.43, printed p.1140. It needs neither abelianness of Q
nor a classification of the normalizer.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A p-subgroup with p-group centralizer has a characteristic-p normalizer. -/
theorem generalizedFitting_normalizer_eq_pCore_of_centralizer_isPGroup
    (Q : Subgroup G) (hq : IsPGroup p Q)
    (hc : IsPGroup p (centralizer (Q : Set G))) :
    generalizedFitting (normalizer (Q : Set G)) =
      pCore p (normalizer (Q : Set G)) := by
  let N := normalizer (Q : Set G)
  have hqcore : Q.subgroupOf N ≤ pCore p N := le_sSup ⟨inferInstance, hq.comap_subtype⟩
  have hccore : (centralizer (Q : Set G)).subgroupOf N ≤ pCore p N :=
    le_sSup ⟨inferInstance, hc.comap_subtype⟩
  apply generalizedFitting_eq_pCore_of_selfCentralizing
  intro x hx
  apply hccore
  intro q hq
  have hh := mem_centralizer_iff.mp hx (⟨q, Q.le_normalizer hq⟩ : N) (hqcore hq)
  exact congrArg Subtype.val hh

end Theory.GroupTheory

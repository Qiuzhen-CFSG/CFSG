module

public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Extension
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.Quasithin.EvenCharacteristic

/-!
# Adjoining a normalizing p-subgroup to a group of characteristic p

If A has self-centralizing p-core and Q is a p-group normalizing A, then
A ⊔ Q has self-centralizing p-core. Work inside the literal join: A is
normal there, and its quotient is an image of Q. The normal-extension
centralizer theorem then applies without any faithfulness assumption on
conjugation by Q.

This is the extension step for invariant parabolics in Aschbacher–Smith,
E.6.8, printed pp.247–248 (`refs/quasithin.pdf`).
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- Characteristic p survives adjoining a normalizing p-group. All normality
is relative to the join; no conjugation kernel is discarded. -/
theorem centralizer_pCore_sup_le {G : Type*} [Group G] (p : ℕ)
    (A Q : Subgroup G)
    (hA : centralizer (pCore p A : Set A) ≤ pCore p A)
    (hQ : IsPGroup p Q) (hN : Q ≤ normalizer (A : Set G)) :
    centralizer (pCore p (A ⊔ Q : Subgroup G) : Set (A ⊔ Q : Subgroup G)) ≤
      pCore p (A ⊔ Q : Subgroup G) := by
  let H := A ⊔ Q
  let N := A.subgroupOf H
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le A.le_normalizer hN)
  have hgen : N ⊔ Q.subgroupOf H = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  exact centralizer_pCore_le_of_normal_pGroup_quotient N
    ((Theory.Quasithin.centralizer_pCore_le_iff p
      (subgroupOfEquivOfLe (show A ≤ H from le_sup_left))).mpr hA)
    (isPGroup_quotient_of_sup_eq_top N (Q.subgroupOf H) hQ.comap_subtype hgen)

end Theory.GroupTheory

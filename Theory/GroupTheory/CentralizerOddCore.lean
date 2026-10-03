module

public import Theory.PPrimeCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Prime-complement cores of element centralizers

An element of order prime to `p` belongs to the `p'`-core of its
centralizer: its cyclic subgroup is central and normal there. The
normalizer of its cyclic subgroup preserves this core, since it
preserves the centralizer and the core is characteristic.

These elementary facts are used in the Borel construction on p.75 of
Fong, J. Algebra 6 (1967).
-/

namespace Subgroup

public theorem mem_pPrimeCore_centralizer
    {G : Type*} [Group G] (p : ℕ) (r : G)
    (hr : Nat.Coprime p (orderOf r)) :
    r ∈ (pPrimeCore p (centralizer ({r} : Set G))).map
      (centralizer ({r} : Set G)).subtype := by
  let C := centralizer ({r} : Set G)
  let rC : C := ⟨r, mem_centralizer_singleton_iff.mpr (Commute.refl r).eq⟩
  have hcentral : rC ∈ center C := by
    apply mem_center_iff.mpr
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp g.property)
  have hZ : zpowers rC ≤ center C := zpowers_le.mpr hcentral
  let : (zpowers rC).Normal := ⟨fun z hz g => by
    have hh := mem_center_iff.mp (hZ hz) g
    simpa only [hh, mul_inv_cancel_right] using hz⟩
  have hcop : Nat.Coprime p (Nat.card (zpowers rC)) := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe rC]
    exact hr
  have hle : zpowers rC ≤ pPrimeCore p C := le_sSup ⟨inferInstance, hcop⟩
  exact ⟨rC, hle (mem_zpowers rC), rfl⟩

public theorem normalizer_le_normalizer_pPrimeCore_centralizer
    {G : Type*} [Group G] (p : ℕ) (r : G) :
    normalizer (zpowers r : Set G) ≤
      normalizer ((pPrimeCore p (centralizer ({r} : Set G))).map
        (centralizer ({r} : Set G)).subtype : Set G) := by
  have h := normalizer_le_normalizer_centralizer (zpowers r)
  rw [zpowers_eq_closure, centralizer_closure] at h
  simpa only [zpowers_eq_closure] using h.trans
    (normalizer_le_normalizer_characteristic_image
      (centralizer ({r} : Set G)) (pPrimeCore p (centralizer ({r} : Set G))))

end Subgroup

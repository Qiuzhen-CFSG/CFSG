module

public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Relative component containment and unequal component orders

Containment of a perfect ambient subgroup in a component of an overgroup
can be tested in that overgroup's literal two-core quotient. Normality is
always relative to the overgroup. If its C-components form a pair of
different orders, conjugation cannot exchange the pair, so both are normal.

These are the lifting and order arguments in Aschbacher--Smith,
14.6.24(3), printed p.1040. The quotient-image containment itself is a
separate input; in that application it follows by excluding a diagonal image.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Transport a component of an overgroup by the same ambient equivalence
on both subgroups. -/
theorem IsCComponent.map_relative_equiv {G' : Type*} [Group G']
    (H B : Subgroup G) (hBH : B ≤ H) (hB : (B.subgroupOf H).IsCComponent)
    (e : G ≃* G') :
    ((B.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom)).IsCComponent := by
  have hc := hB.map_equiv (e.subgroupMap H)
  have he : (B.subgroupOf H).map (e.subgroupMap H).toMonoidHom =
      (B.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom) := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact mem_map_of_mem e.toMonoidHom hb
    · rintro ⟨b,hb,hbx⟩
      exact ⟨⟨b,hBH hb⟩,hb,Subtype.ext hbx⟩
  rwa [he] at hc

/-- Perfect containment lifts through the literal two-core quotient of H,
without requiring H or either ambient subgroup to be normal in G. -/
theorem perfect_le_relative_cComponent_of_twoCore_image_le
    (H B J : Subgroup G) [Group.IsPerfect B]
    (hBH : B ≤ H) (hJH : J ≤ H) (hJ : (J.subgroupOf H).IsCComponent)
    (himage : (B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≤
      (J.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) : B ≤ J := by
  let : Group.IsPerfect (B.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBH).symm.surjective
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have h := perfect_le_cComponent_of_map_le hJ (pCore 2 H) himage
  simpa only [map_subgroupOf_eq_of_le hBH, map_subgroupOf_eq_of_le hJH]
    using map_mono (f := H.subtype) h

omit [Finite G] in
/-- An invariant pair of C-components of unequal orders consists of normal
subgroups. No normality of the components is assumed. -/
theorem cComponent_pair_normal_of_card_ne
    (B C : Subgroup G) (hB : B.IsCComponent) (hC : C.IsCComponent)
    (hpair : ∀ J : Subgroup G, J.IsCComponent → J = B ∨ J = C)
    (hcard : Nat.card B ≠ Nat.card C) : B.Normal ∧ C.Normal := by
  have step (A D : Subgroup G) (hA : A.IsCComponent)
      (hclass : ∀ J : Subgroup G, J.IsCComponent → J = A ∨ J = D)
      (hne : Nat.card A ≠ Nat.card D) : A.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff]
    intro g _
    apply mem_normalizer_iff_map_conj_eq.mpr
    rcases hclass _ (hA.map_equiv (MulAut.conj g)) with he | he
    · exact he
    · have hc := card_map_of_injective (K := A)
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
      rw [he] at hc
      exact (hne hc.symm).elim
  exact ⟨step B C hB hpair hcard,
    step C B hC (fun J hJ => (hpair J hJ).symm) hcard.symm⟩

omit [Finite G] in
/-- The unequal-order argument inside a specified overgroup, retaining the
ambient component subgroups instead of replacing them by abstract copies. -/
theorem relative_cComponent_pair_normal_of_card_ne
    (H B C : Subgroup G) (hBH : B ≤ H) (hCH : C ≤ H)
    (hB : (B.subgroupOf H).IsCComponent) (hC : (C.subgroupOf H).IsCComponent)
    (hpair : ∀ J : Subgroup H, J.IsCComponent →
      J = B.subgroupOf H ∨ J = C.subgroupOf H)
    (hcard : Nat.card B ≠ Nat.card C) :
    (B.subgroupOf H).Normal ∧ (C.subgroupOf H).Normal := by
  apply cComponent_pair_normal_of_card_ne _ _ hB hC hpair
  simpa only [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hCH).toEquiv] using hcard

end Subgroup

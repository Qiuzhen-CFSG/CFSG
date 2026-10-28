module
public import ABG.ChapterII.Section2.QDCharacterization
public import ABG.ChapterII.Section2.SylowShapeTransport
public import ABG.ChapterII.Section2.CoreFreeSimpleNormal

/-!
# The simple normal QD subgroup of the odd-core quotient

Every finite QD-group has a simple normal QD-subgroup of odd index modulo
its odd core. This is Proposition 2 in Alperin--Brauer--Gorenstein,
Chapter II, Section 2 (article pages 15--16), for both Sylow shapes.

The no-index-two characterization and the preserved Sylow shape show that
the odd-core quotient is again QD. Its odd core is trivial, so the proved
minimal-normal simplicity argument supplies a simple normal subgroup of
odd index. The ambient Sylow subgroup lies inside it and retains its
quasi-dihedral or wreathed shape under restriction. Simplicity excludes
index two, recovering the full QD fusion pattern, not only Sylow shape.

This is the source reduction used to apply simultaneous induction to
proper QD sections in the three main theorems. It does not assume any of
the main theorems or replace the full QD predicate by a structural shortcut.
-/

namespace ABG

private theorem four_le_card_of_shape {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) :
    4 ≤ Nat.card G := by
  have hfour : 4 ≤ Nat.card S := by
    rcases hS with ⟨n, hn, hc, _⟩ | ⟨n, hn, hc, _⟩
    · rw [hc]
      exact (by norm_num : 4 = 2 ^ 2).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    · rw [hc]
      exact (by norm_num : 4 = 2 ^ 2).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
  exact hfour.trans (Nat.le_of_dvd Nat.card_pos
    (Subgroup.card_subgroup_dvd_card (S : Subgroup G)))

private theorem qd_of_simple_of_shape {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) :
    IsQDGroup G := by
  apply (isQDGroup_iff_no_normal_index_two S hS).mpr
  intro N hN hn
  rcases hN.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.index_bot] at hn
    have := four_le_card_of_shape S hS
    omega
  · simp [h] at hn

private theorem qd_oddCore_quotient {G : Type*} [Group G] [Finite G]
    (hG : IsQDGroup G) : IsQDGroup (G ⧸ pPrimeCore 2 G) := by
  obtain ⟨S, hS⟩ := hG.sylow_shape_oddCore_quotient
  apply (isQDGroup_iff_no_normal_index_two S hS).mpr
  intro N hN hn
  let : N.Normal := hN
  exact hG.no_normal_index_two
    (N.comap (QuotientGroup.mk' (pPrimeCore 2 G))) inferInstance
    ((N.index_comap_of_surjective
      (QuotientGroup.mk'_surjective (pPrimeCore 2 G))).trans hn)

/-- The odd-core quotient of a QD-group has a simple normal QD-subgroup of odd index. -/
public theorem IsQDGroup.exists_simple_normal_oddCoreQuotient
    {G : Type*} [Group G] [Finite G] (hG : IsQDGroup G) :
    ∃ L : Subgroup (G ⧸ pPrimeCore 2 G),
      L.Normal ∧ IsSimpleGroup L ∧ IsQDGroup L ∧ Odd L.index := by
  let H := G ⧸ pPrimeCore 2 G
  have hH : IsQDGroup H := qd_oddCore_quotient hG
  have hcore : pPrimeCore 2 H = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2)
  obtain ⟨L, hLn, hLs, hLi⟩ := hH.exists_simple_normal_of_oddCore_eq_bot hcore
  let : L.Normal := hLn
  let : IsSimpleGroup L := hLs
  obtain ⟨S, hS⟩ := hG.sylow_shape_oddCore_quotient
  have hSL : (S : Subgroup H) ≤ L := sylow_le_odd_index S L hLi
  let R : Sylow 2 L := S.subtype hSL
  let e : R ≃* S := Subgroup.subgroupOfEquivOfLe hSL
  have hR : Stellmacher.IsSemidihedralGroup R ∨ IsWreathedGroup R := by
    rcases hS with h | ⟨n, h⟩
    · exact Or.inl (semidihedral_equiv e.symm h)
    · exact Or.inr ⟨n, wreathed_equiv e.symm h⟩
  exact ⟨L, hLn, hLs, qd_of_simple_of_shape R hR, hLi⟩

end ABG


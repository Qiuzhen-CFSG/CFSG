module
public import Theory.GroupTheory.PPrimeCorePGroupQuotient

/-!
# Prime-complement cores across a prime-power extension

If a normal subgroup N has p-group quotient, the p'-core of the ambient
finite group lies in N. Restricting it to N gives one inclusion, while
characteristicity of the core of N gives the reverse inclusion.

This is the core equality in the Thompson–Bender step of GLS, Volume 4,
Chapter 2, Lemma 7.6, applied to N = O_{2'}(D) in W₁N.
-/

/-- A normal subgroup with p-group quotient has the same p'-core as its
ambient group, under the actual subgroup inclusion. -/
public theorem pPrimeCore_map_eq_of_isPGroup_quotient
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hQ : IsPGroup p (G ⧸ N)) :
    (pPrimeCore p N).map N.subtype = pPrimeCore p G := by
  apply le_antisymm (pPrimeCore_map_subtype_le_pPrimeCore_of_normal p N)
  have hON := pPrimeCore_le_of_isPGroup_quotient p N hQ
  have hcore : (pPrimeCore p G).subgroupOf N ≤ pPrimeCore p N := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    exact (pPrimeCore_coprime_card (p := p) (G := G)).of_dvd_right
      ((pPrimeCore p G).card_comap_dvd_of_injective N.subtype N.subtype_injective)
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hON hx⟩, hcore hx, rfl⟩

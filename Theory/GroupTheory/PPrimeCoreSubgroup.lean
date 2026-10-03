module

public import Theory.PPrimeCore

/-!
# Prime-subgroup injection modulo the prime-complement core

The quotient by the p′-core is injective on each p-subgroup of a finite group.
The two subgroup orders are coprime, so their intersection, and hence the
kernel of the restricted quotient map, is trivial.

This is the coprime-kernel argument also used in
`FeitThompson/BGsection6/Defs.lean`. Its historical public theorem remains there;
this module supplies the independent downward interface for Theory consumers.
-/

/-- Quotienting by the p′-core is injective on a p-subgroup. -/
public theorem IsPGroup.quotient_pPrimeCore_injective
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (hHp : IsPGroup p H) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore p G)).comp H.subtype) := by
  let q : G →* G ⧸ pPrimeCore p G := QuotientGroup.mk' (pPrimeCore p G)
  have hcoprime :
      Nat.Coprime (Nat.card H) (Nat.card (pPrimeCore p G)) := by
    rcases IsPGroup.iff_card.mp hHp with ⟨n, hcard⟩
    rw [hcard]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
  have hinf_bot : H ⊓ pPrimeCore p G = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcoprime).eq_bot
  have hker_bot :
      (((q.comp H.subtype)).ker : Subgroup H) = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxM : ((x : H) : G) ∈ pPrimeCore p G := by
        exact
          (QuotientGroup.eq_one_iff (N := pPrimeCore p G) (x := ((x : H) : G))).1 hx
      have hxbot : ((x : H) : G) ∈ (⊥ : Subgroup G) := by
        rw [← hinf_bot]
        exact ⟨x.2, hxM⟩
      simpa using hxbot
    · intro hx
      change q ((x : H) : G) = 1
      have hx1 : x = 1 := by
        simpa [Subgroup.mem_bot] using hx
      rw [hx1]
      simp [q]
  exact (MonoidHom.ker_eq_bot_iff (q.comp H.subtype)).1 hker_bot

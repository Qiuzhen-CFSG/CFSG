module
public import FeitThompson.BGsection3.Defs

public import FeitThompson.GeneratorRank
public import FeitThompson.BGsection4.theorem_4_18_c
/-! # Theorem 4.18(d) from BG Section 4 -/

universe u

section Main

open scoped FixedPoints

public theorem theorem_4_18_d {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hsolv : IsSolvable G) (hodd : Odd (Nat.card G)) (hp_mem : p ∣ Nat.card G)
    (hrank : primeRank p G ≤ 2) :
    ∀ H : Subgroup (derivedSubgroup G), Nat.Coprime p (Nat.card H) → H ≤ pPrimeCore p (derivedSubgroup G) := by
  intro H hHcop
  rcases theorem_4_18_c (G := G) (p := p) hsolv hodd hp_mem hrank with ⟨N, hNnorm, hNcop, hquotP⟩
  let q : derivedSubgroup G →* (derivedSubgroup G) ⧸ N := QuotientGroup.mk' N
  have hHmap_p : IsPGroup p (H.map q) := hquotP.to_subgroup (H.map q)
  have hHmap_coprime : Nat.Coprime p (Nat.card (H.map q)) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := H) q) hHcop
  have hHmap_card_eq_one : Nat.card (H.map q) = 1 := by
    rcases hHmap_p.card_eq_or_dvd with h1 | hpdvd
    · exact h1
    · exfalso
      exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hHmap_coprime) hpdvd
  have hHmap_bot : H.map q = ⊥ := Subgroup.card_eq_one.mp hHmap_card_eq_one
  have hHle_N : H ≤ N := by
    have hHle_ker : H ≤ q.ker := by
      intro x hx
      have hxmap : q x ∈ H.map q := Subgroup.mem_map_of_mem q hx
      rw [hHmap_bot] at hxmap
      have hx1 : q x = 1 := by simpa using hxmap
      simpa [MonoidHom.mem_ker] using hx1
    have hHle_ker' : H ≤ (QuotientGroup.mk' N).ker := by
      simpa [q] using hHle_ker
    refine hHle_ker'.trans ?_
    intro x hx
    have hx1 : (QuotientGroup.mk' N) x = 1 := by
      simpa [MonoidHom.mem_ker] using hx
    exact (QuotientGroup.eq_one_iff (N := N) (x := x)).1 hx1
  exact hHle_N.trans (le_sSup ⟨hNnorm, hNcop⟩)

end Main

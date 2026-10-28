module

public import Theory.SpecificGroups.ProjectiveLinear.EvenOddTori.Reflection

/-!
# Cyclic subgroups and the two PSL₂ tori

The concrete Huppert element partition puts the generator of an odd cyclic
subgroup in a split or nonsplit torus. Cardinality and coprimality identify the
partition tori with the reflection tori from II.8.3 and II.8.4, so the same
witnesses have both coverage and full subgroup-normalizer control.

This is the cyclic input to the odd-subgroup conclusion of GLS4, 4.3.7,
used in GLS4, 2.17.5. Cyclicity of an arbitrary odd subgroup is proved in the
parent module, rather than assumed here in that final conclusion.
-/

open Subgroup
open scoped Pointwise IsMulCommutative
namespace BenderSuzuki.MatrixGroups.EvenOddTori

private theorem cyclic_le_cover {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (U S : Subgroup G)
    (hcover : ∀ x : G, x ≠ 1 → ∃ T : Subgroup G, x ∈ T ∧
      ((∃ g, T = (P : Subgroup G).map (MulAut.conj g).toMonoidHom) ∨
       (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
       (∃ g, T = S.map (MulAut.conj g).toMonoidHom)))
    (C : Subgroup G) (hC : IsCyclic C) (hodd : Odd (Nat.card C)) (hne : C ≠ ⊥) :
    (∃ g, C ≤ U.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g, C ≤ S.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨x, rfl⟩ := C.isCyclic_iff_exists_zpowers_eq_top.mp hC
  have hx : x ≠ 1 := by simpa using hne
  obtain ⟨T, hxT, hT⟩ := hcover x hx
  rcases hT with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · have hd := (P.isPGroup'.map (MulAut.conj g).toMonoidHom).dvd_orderOf
      (g := ⟨x, hxT⟩) (fun h => hx (congrArg Subtype.val h))
    rw [Subgroup.orderOf_mk] at hd
    exact (hodd.not_two_dvd_nat (by simpa only [Nat.card_zpowers] using hd)).elim
  · exact Or.inl ⟨g, zpowers_le.mpr hxT⟩
  · exact Or.inr ⟨g, zpowers_le.mpr hxT⟩

private theorem binary_arithmetic {q n : ℕ} (hq : q = 2 ^ n) (hn : 2 ≤ n) :
    4 ≤ q ∧ Odd (q - 1) ∧ Odd (q + 1) ∧
    Nat.gcd (q - 1) 2 = 1 ∧ Nat.Coprime (q - 1) (q + 1) := by
  have h4 : 4 ≤ q := by
    rw [hq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
  have he : Even q := by rw [hq]; exact even_two.pow_of_ne_zero (by omega)
  obtain ⟨k, hk⟩ := he
  have hm : Odd (q - 1) := ⟨k - 1, by omega⟩
  have hp : Odd (q + 1) := ⟨k, by omega⟩
  refine ⟨h4, hm, hp, hm.coprime_two_right, ?_⟩
  have hsum : q + 1 = (q - 1) + 2 := by omega
  rw [hsum, Nat.coprime_self_add_right]
  exact hm.coprime_two_right

-- Both members of the element partition carry the reflection data.
private theorem partition_reflections {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    ∃ U S : Subgroup (PSL2MatrixGroup F),
      ReflectionData U ∧ Nat.card U = Nat.card F - 1 ∧
      ReflectionData S ∧ Nat.card S = Nat.card F + 1 ∧
      ∀ C : Subgroup (PSL2MatrixGroup F), IsCyclic C → Odd (Nat.card C) → C ≠ ⊥ →
        (∃ g, C ≤ U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, C ≤ S.map (MulAut.conj g).toMonoidHom) := by
  classical
  obtain ⟨h4, hm, hp, hgcd, hcop⟩ := binary_arithmetic hF hn
  let P : Sylow 2 (PSL2MatrixGroup F) := default
  obtain ⟨U, S, hU, hcU, hS, hcS, hpart⟩ :=
    BenderSuzuki.External.huppert_II_8_5_a_psl2_partition hF P
  simp only [hgcd, Nat.div_one] at hcU hcS
  have hcover := cyclic_le_cover P U S (fun x hx => (hpart x hx).exists)
  have href (A : Subgroup (PSL2MatrixGroup F)) (dA : ReflectionData A)
      (hA : Nat.card A = Nat.card F - 1 ∨ Nat.card A = Nat.card F + 1) :
      (Nat.card A = Nat.card F - 1 → ReflectionData U) ∧
      (Nat.card A = Nat.card F + 1 → ReflectionData S) := by
    have hA1 : 1 < Nat.card A := by rcases hA with h | h <;> omega
    have hAne : A ≠ ⊥ := by intro h; simp [h] at hA1
    rcases hcover A dA.cyclic dA.odd hAne with ⟨g, hle⟩ | ⟨g, hle⟩
    · have hc : Nat.card (U.map (MulAut.conj g).toMonoidHom) = Nat.card F - 1 :=
        (card_map_of_injective (MulAut.conj g).injective).trans hcU
      have hd := card_dvd_of_le hle
      rw [hc] at hd
      have hnot : Nat.card A ≠ Nat.card F + 1 := by
        intro he
        rw [he] at hd
        have := Nat.le_of_dvd (by omega : 0 < Nat.card F - 1) hd
        omega
      have heq : A = U.map (MulAut.conj g).toMonoidHom :=
        eq_of_le_of_card_ge hle (by rcases hA with h | h <;> omega)
      have hback : A.map (MulAut.conj g).symm.toMonoidHom = U :=
        (map_symm_eq_iff_map_eq U (e := MulAut.conj g)).mpr heq.symm
      exact ⟨fun _ => hback ▸ dA.map (MulAut.conj g).symm, fun h => (hnot h).elim⟩
    · have hc : Nat.card (S.map (MulAut.conj g).toMonoidHom) = Nat.card F + 1 :=
        (card_map_of_injective (MulAut.conj g).injective).trans hcS
      have hd := card_dvd_of_le hle
      rw [hc] at hd
      have hnot : Nat.card A ≠ Nat.card F - 1 := by
        intro he
        rw [he] at hd
        have := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hd
        omega
      have heq : A = S.map (MulAut.conj g).toMonoidHom :=
        eq_of_le_of_card_ge hle (by rcases hA with h | h <;> omega)
      have hback : A.map (MulAut.conj g).symm.toMonoidHom = S :=
        (map_symm_eq_iff_map_eq S (e := MulAut.conj g)).mpr heq.symm
      exact ⟨fun h => (hnot h).elim, fun _ => hback ▸ dA.map (MulAut.conj g).symm⟩
  obtain ⟨A, w, hAc, hAn, hwN, hwA, hww, hwi, _, hNA⟩ :=
    BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data hF
  simp only [hgcd, Nat.div_one] at hAn
  have dA : ReflectionData A := ⟨hAc, hAn ▸ hm, w, hwN, hwA, hww, hwi, hNA⟩
  obtain ⟨B, v, hBc, hBn, hvN, hvB, hvv, hvi, _, hNB⟩ :=
    BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data hF
  simp only [hgcd, Nat.div_one] at hBn
  have dB : ReflectionData B := ⟨hBc, hBn ▸ hp, v, hvN, hvB, hvv, hvi, hNB⟩
  exact ⟨U, S, (href A dA (Or.inl hAn)).1 hAn, hcU,
    (href B dB (Or.inr hBn)).2 hBn, hcS, hcover⟩

/-- Every odd cyclic subgroup lies in a full split or nonsplit torus, with
normalizer and reflection data inherited from the actual matrix construction. -/
public theorem exists_torus_of_cyclic {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (C : Subgroup (PSL2MatrixGroup F)) (hC : IsCyclic C) (hodd : Odd (Nat.card C)) :
    ∃ T : Subgroup (PSL2MatrixGroup F), C ≤ T ∧ ReflectionData T ∧
      (Nat.card T = Nat.card F - 1 ∨ Nat.card T = Nat.card F + 1) := by
  obtain ⟨U, S, dU, hcU, dS, hcS, hcover⟩ := partition_reflections hF hn
  by_cases hne : C = ⊥
  · exact ⟨U, hne ▸ bot_le, dU, Or.inl hcU⟩
  · rcases hcover C hC hodd hne with ⟨g, hle⟩ | ⟨g, hle⟩
    · exact ⟨_, hle, dU.map (MulAut.conj g),
        Or.inl ((card_map_of_injective (MulAut.conj g).injective).trans hcU)⟩
    · exact ⟨_, hle, dS.map (MulAut.conj g),
        Or.inr ((card_map_of_injective (MulAut.conj g).injective).trans hcS)⟩

/-- Any full cyclic torus of either order has the concrete reflection normalizer,
including normalizers of its arbitrary nontrivial subgroups. -/
public theorem reflectionData_of_cyclic_card {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (C : Subgroup (PSL2MatrixGroup F)) (hC : IsCyclic C)
    (hc : Nat.card C = Nat.card F - 1 ∨ Nat.card C = Nat.card F + 1) :
    ReflectionData C := by
  obtain ⟨h4, hm, hp, _, hcop⟩ := binary_arithmetic hF hn
  have hodd : Odd (Nat.card C) := by rcases hc with h | h <;> simpa [h]
  obtain ⟨T, hCT, dT, ht⟩ := exists_torus_of_cyclic hF hn C hC hodd
  have hd := card_dvd_of_le hCT
  have he : C = T := by
    apply eq_of_le_of_card_ge hCT
    rcases hc with hc | hc <;> rcases ht with ht | ht
    · omega
    · rw [hc, ht] at hd
      have := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hd
      omega
    · omega
    · omega
  exact he ▸ dT

end BenderSuzuki.MatrixGroups.EvenOddTori

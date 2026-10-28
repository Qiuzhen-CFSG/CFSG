module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Tori.Reflected

/-!
# The prime dihedral seed in the actual PSL₂ model

Huppert's split and nonsplit constructions give the two reflected cyclic tori.
Choose the torus of even order, and transport both the torus and its reflection
through the supplied group isomorphism. Its order exceeds two for odd prime
field order greater than five. The reflected-cyclic extraction then constructs
a prime dihedral subgroup and its central involution.

Source: Huppert II.8.3--4, applied to the torus branch of Aschbacher--Smith
E.1.14(6), citing Aschbacher (1982), Lemma 4.10.
-/

public section

open Subgroup GorensteinWalter BenderSuzuki.External

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Tori

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- The split or nonsplit torus in the actual PSL₂ model supplies the prime
dihedral seed. Its construction retains a central involution for fusion. -/
theorem prime_dihedral_seed {p : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hp5 : 5 < p) (hF : Nat.card F = p) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) (hT : Nat.card T = 4) :
    ∃ (r : ℕ) (D : Subgroup G) (t : G), r.Prime ∧ Odd r ∧
      t ∈ D ∧ IsInvolution t ∧ D ≤ centralizer ({t} : Set G) ∧
      Nonempty (D ≃* DihedralGroup (2 * r)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp7 : 7 ≤ p := by
    obtain ⟨k, hk⟩ := hpo
    omega
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    apply Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
    apply Nat.dvd_gcd _ (dvd_refl 2)
    rw [hF]
    obtain ⟨k, hk⟩ := hpo
    exact ⟨k, by omega⟩
  have hpow : Nat.card F = p ^ 1 := by simpa using hF
  have htorus : ∃ (U : Subgroup (PSL2 F)) (w : PSL2 F),
      IsCyclic U ∧ 2 ∣ Nat.card U ∧ 2 < Nat.card U ∧ w ∉ U ∧
        w * w = 1 ∧ ∀ x : PSL2 F, x ∈ U → w * x * w⁻¹ = x⁻¹ := by
    rcases Nat.even_or_odd ((p - 1) / 2) with hs | hn
    · obtain ⟨U, w, hUc, hUcard, _, hwU, hw2, hwi, _, _⟩ :=
        huppert_II_8_3_split_torus_reflection_data (F := F) hpow
      have hc : Nat.card U = (p - 1) / 2 := by
        rw [hgcd, hF] at hUcard
        exact hUcard
      refine ⟨U, w, hUc, ?_, ?_, hwU, hw2, hwi⟩
      · rw [hc]; exact hs.two_dvd
      · rw [hc]; omega
    · obtain ⟨U, w, hUc, hUcard, _, hwU, hw2, hwi, _, _⟩ :=
        huppert_II_8_4_nonsplit_torus_reflection_data (F := F) hpow
      have hc : Nat.card U = (p + 1) / 2 := by
        rw [hgcd, hF] at hUcard
        exact hUcard
      have he : 2 ∣ (p + 1) / 2 := by
        obtain ⟨k, hk⟩ := hn
        exact ⟨k + 1, by omega⟩
      refine ⟨U, w, hUc, ?_, ?_, hwU, hw2, hwi⟩
      · rw [hc]; exact he
      · rw [hc]; omega
  obtain ⟨U, w, hUc, hUeven, hUlarge, hwU, hw2, hwi⟩ := htorus
  let V : Subgroup G := U.map e.symm.toMonoidHom
  let eV : U ≃* V := U.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  have hVcard : Nat.card V = Nat.card U := (Nat.card_congr eV.toEquiv).symm
  let : IsCyclic U := hUc
  have hVc : IsCyclic V := isCyclic_of_surjective eV eV.surjective
  have hwV : e.symm w ∉ V := by
    rintro ⟨u, hu, heq⟩
    exact hwU (e.symm.injective heq ▸ hu)
  have hwV2 : e.symm w * e.symm w = 1 := by
    simpa only [map_mul, map_one] using congrArg e.symm hw2
  have hVinv : ∀ x : G, x ∈ V → e.symm w * x * (e.symm w)⁻¹ = x⁻¹ := by
    rintro x ⟨u, hu, rfl⟩
    change e.symm w * e.symm u * (e.symm w)⁻¹ = (e.symm u)⁻¹
    simpa only [map_mul, map_inv] using congrArg e.symm (hwi u hu)
  exact prime_dihedral_of_reflected_cyclic T hT V hVc
    (by rw [hVcard]; exact hUeven) (by rw [hVcard]; exact hUlarge)
    (e.symm w) hwV hwV2 hVinv

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Tori

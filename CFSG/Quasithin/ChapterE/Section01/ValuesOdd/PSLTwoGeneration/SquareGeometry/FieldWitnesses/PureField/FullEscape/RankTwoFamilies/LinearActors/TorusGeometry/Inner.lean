module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry.Layers
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry.Reflected
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes

/-!
# Odd torus escape for inner four-groups

Restrict the actor and Sylow to PSL₂, enlarge the proper intersection with
the prescribed overgroup to a maximal subgroup, and select its missing
centralizer prime. The reflected involution torus supplies the characteristic
odd prime core. Its full semilinear centralizer normalization and escaping
commutator follow from `reflected_prime_escape`.

The missing-prime theorem includes p = 5; no extra small-prime assumption
or local-generation premise is used.
Source: Aschbacher–Smith E.1.2 and E.1.14(6), pp.209–210, 214;
Aschbacher (1982), Lemma 4.10.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry
variable {F : Type*} [Field F] [Finite F] [Finite (PGammaL2 F)]

/-- An inner four-group has a full-centralizer-normalized odd commutator
escaping every proper Sylow overgroup, including in characteristic five. -/
theorem inner_placement {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p ^ 2) (hp5 : 5 ≤ p)
    (T : Sylow 2 (PGammaL2 F)) (A M : Subgroup (PGammaL2 F))
    (hA : IsKleinFour A) (hAT : A ≤ (T : Subgroup _))
    (hAJ : A ≤ pGammaL2PSLRange F) (hM : M ≠ ⊤) (hTM : (T : Subgroup _) ≤ M) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup (PGammaL2 F),
      IsPGroup r X ∧ centralizer (A : Set (PGammaL2 F)) ≤ normalizer (X : Set _) ∧
      ¬ ⁅X, A⁆ ≤ M := by
  classical
  let f : PSL2 F →* PGammaL2 F := SemidirectProduct.inl.comp
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))
  have hf : Function.Injective f := SemidirectProduct.inl_injective.comp
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let : f.range.Normal := pGammaL2_psl_range_normal_of_odd_prime_power F
    ⟨p, 2, hp, ho, by decide, hF⟩
  let A₀ := A.comap f
  have hA₀ : IsKleinFour A₀ := kleinFour_comap f hf A hA hAJ
  obtain ⟨Q, hQ⟩ := sylow_comap_normal f hf T
  have hA₀Q : A₀ ≤ (Q : Subgroup _) := by rw [hQ]; exact comap_mono hAT
  have hproper : M.comap f ≠ ⊤ := comap_ne_top_of_supplement f T M
    (sylow_sup_psl hp ho hF T) hTM hM
  obtain ⟨N, hN, hMN⟩ := (eq_top_or_exists_le_coatom (M.comap f)).resolve_left hproper
  have hQN : (Q : Subgroup _) ≤ N := by rw [hQ]; exact (comap_mono hTM).trans hMN
  obtain ⟨z, r, hzA, hz1, hr, hro, hrq, hrN⟩ :=
    LinearWitnesses.InnerPlacement.CentralizerPrimes.missing_centralizer_prime
      hp ho hp5 hF Q A₀ N hA₀ hA₀Q hN hQN
  let : IsKleinFour A₀ := hA₀
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨z, hzA⟩ : A₀))
  obtain ⟨U, w, hU, _hzU, hw, hwU, hinv, hC, hUeven, hUcard⟩ :=
    psl2_reflected_torus_card (K := F) ⟨p, 2, hp, ho, by decide, hF⟩ ⟨hz1, hz2⟩
  have hUc : Nat.card U = (p ^ 2 - 1) / 2 := by
    rcases hUcard with h | h
    · simpa only [hF] using h
    · have hoddhalf : Odd ((p ^ 2 + 1) / 2) := by
        obtain ⟨k, rfl⟩ := ho
        have he : (2 * k + 1) ^ 2 + 1 = 2 * (2 * (k * k + k) + 1) := by ring
        rw [he, Nat.mul_div_right _ (by decide : 0 < 2)]
        exact ⟨k * k + k, rfl⟩
      have hh : Odd (Nat.card U) := by rw [h, hF]; exact hoddhalf
      exact (hh.not_two_dvd_nat hUeven.two_dvd).elim
  have hrM : ¬ r ∣ Nat.card ((centralizer ({z} : Set (PSL2 F))).subgroupOf (M.comap f)) := by
    intro hd
    apply hrN
    let j : (centralizer ({z} : Set (PSL2 F))).subgroupOf (M.comap f) →*
        (centralizer ({z} : Set (PSL2 F))).subgroupOf N :=
      { toFun := fun x => ⟨⟨x.val.val, hMN x.val.property⟩, x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun a => a.val.val) h))
    exact hd.trans (Subgroup.card_dvd_of_injective j hj)
  obtain ⟨X, hX, hn, hmove⟩ := reflected_prime_escape f hf A₀ U hA₀ hU z w hzA
    hwU (by simpa only [pow_two] using hw.2) hinv hC hr hro (hUc ▸ hrq) M hrM
  have hmap : A₀.map f = A := map_comap_eq_self hAJ
  rw [hmap] at hn hmove
  exact ⟨r, hr, hro, X, hX, hn, hmove⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry

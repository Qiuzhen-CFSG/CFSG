module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry.Layers
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry.Reflected
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement

/-!
# Odd torus escape for outer linear four-groups

Align an outer involution of the original actor with the low-two-part
torus. In square degree this torus is nonsplit, so its odd prime divisor
divides p²+1. The supplied PGL₂ overgroup models force a Sylow overgroup
to be split, excluding that divisor. Conjugation is retained in the actual
embedding into the semilinear group, so characteristicity provides full
centralizer normalization. This includes outer actors at p = 3.

Source: Aschbacher–Smith E.1.2 and E.1.14(6), pp.209–210, 214;
Aschbacher (1982), Lemma 4.10.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry
variable {F : Type*} [Field F] [Finite F] [Finite (PGammaL2 F)]

/-- An outer linear four-group has a normalized escaping odd commutator;
only the indicated PGL₂ overgroup classification is assumed. -/
theorem outer_placement {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (hover : ∀ (Q : Sylow 2 (PGL2 F)) (N : Subgroup (PGL2 F)),
      IsCoatom N → (Q : Subgroup _) ≤ N → PrimeGeometry.Diagonal.SylowOvergroupModel F N)
    (T : Sylow 2 (PGammaL2 F)) (A M : Subgroup (PGammaL2 F))
    (hA : IsKleinFour A)
    (hAL : A ≤ pGammaL2PGLRange F) (hAJ : ¬ A ≤ pGammaL2PSLRange F)
    (hM : M ≠ ⊤) (hTM : (T : Subgroup _) ≤ M) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup (PGammaL2 F),
      IsPGroup r X ∧ centralizer (A : Set (PGammaL2 F)) ≤ normalizer (X : Set _) ∧
      ¬ ⁅X, A⁆ ≤ M := by
  classical
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let i : PGL2 F →* PGammaL2 F := SemidirectProduct.inl
  let B := A.comap i
  have hB : IsKleinFour B := kleinFour_comap i SemidirectProduct.inl_injective A hA hAL
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, ho, by decide, hF⟩
  have hq3 : 3 < Nat.card F := by omega
  have hBJ : ¬ B ≤ commutator (PGL2 F) := by
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three F hq hq3]
    intro h
    apply hAJ
    intro x hx
    obtain ⟨y, hy⟩ := hAL hx
    change i y = x at hy
    obtain ⟨z, hz⟩ := h (show y ∈ B by change i y ∈ A; simpa only [hy] using hx)
    exact ⟨z, by change i (Matrix.ProjectiveSpecialLinearGroup.toPGL z) = x; rw [hz]; exact hy⟩
  have hJ : (commutator (PGL2 F)).index = 2 := by
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three F hq hq3]
    exact pgl2_psl2Range_index_eq_two F hq
  obtain ⟨s, t, hsB, _htB, hs, ht, hst, hsJ, htJ⟩ :=
    PrimeGeometry.Diagonal.outer_kleinFour_pair (commutator (PGL2 F)) B hJ hB hBJ
  obtain ⟨P, m, eP, d, a, hsa, _hta⟩ :=
    pgl2_reflected_tori_pair_alignment F hq hq3 s t hs ht hst hsJ htJ
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd d.R_card_gt_one.ne'
  have hro : Odd r := d.R_card_odd.of_dvd_nat hrd
  have hrU : r ∣ Nat.card d.U := hrd.trans (card_dvd_of_le (by
    rw [d.R_eq]; exact inf_le_left))
  have hrplus : r ∣ p ^ 2 + 1 := by
    rcases d.U_card with h | h
    · have hh := d.U_half_odd
      rw [h, hF] at hh
      obtain ⟨k, hk⟩ := Nat.eight_dvd_sq_sub_one_of_odd ho
      have he : (p ^ 2 - 1) / 2 = 4 * k := by omega
      rw [he] at hh
      exact (hh.not_two_dvd_nat ⟨2 * k, by omega⟩).elim
    · simpa only [h, hF] using hrU
  obtain ⟨Q, hQ⟩ := sylow_comap_normal i SemidirectProduct.inl_injective T
  have hsupp : (T : Subgroup _) ⊔ i.range = ⊤ := by
    apply top_unique
    rw [← sylow_sup_psl hp ho hF T]
    apply sup_le_sup_left
    rintro _ ⟨x, rfl⟩
    exact ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL x, rfl⟩
  have hproper := comap_ne_top_of_supplement i T M hsupp hTM hM
  obtain ⟨N, hN, hMN⟩ := (eq_top_or_exists_le_coatom (M.comap i)).resolve_left hproper
  have hQN : (Q : Subgroup _) ≤ N := by rw [hQ]; exact (comap_mono hTM).trans hMN
  obtain ⟨eN⟩ := LinearWitnesses.DiagonalPlacement.split_overgroup_of_model ho hF Q N hQN
    (hover Q N hN hQN)
  have hrN : ¬ r ∣ Nat.card N := by
    rw [Nat.card_congr eN.toEquiv, DihedralGroup.nat_card, hF]
    have hr2 : ¬ r ∣ 2 := by
      intro hh
      have he : r = 2 := le_antisymm (Nat.le_of_dvd (by decide) hh) hr.two_le
      subst r
      exact hro.not_two_dvd_nat (dvd_refl 2)
    intro hd
    have hm := (hr.dvd_mul.mp hd).resolve_left hr2
    apply hr2
    convert Nat.dvd_sub hrplus hm using 1; omega
  let e := MulAut.conj a
  let f := i.comp e.toMonoidHom
  have hf : Function.Injective f := SemidirectProduct.inl_injective.comp e.injective
  have hfr : f.range = i.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, by change i (e (e.symm y)) = i y; rw [e.apply_symm_apply]⟩
  let : f.range.Normal := by rw [hfr]; infer_instance
  have hAf : A ≤ f.range := by rw [hfr]; exact hAL
  let A₀ := A.comap f
  have hA₀ := kleinFour_comap f hf A hA hAf
  have hsA₀ : d.s ∈ A₀ := by
    change i (e d.s) ∈ A
    change i (a * d.s * a⁻¹) ∈ A
    rw [← hsa]
    exact hsB
  have hrM : ¬ r ∣ Nat.card ((centralizer ({d.s} : Set (PGL2 F))).subgroupOf (M.comap f)) := by
    intro hd
    apply hrN
    let j : (centralizer ({d.s} : Set (PGL2 F))).subgroupOf (M.comap f) →* N :=
      { toFun := fun x => ⟨e x.val.val, hMN x.val.property⟩
        map_one' := by apply Subtype.ext; exact e.map_one
        map_mul' := fun x y => by apply Subtype.ext; exact e.map_mul x.val.val y.val.val }
    have hj : Function.Injective j := by
      intro x y h
      exact Subtype.ext (Subtype.ext (e.injective (congrArg Subtype.val h)))
    exact hd.trans (Subgroup.card_dvd_of_injective j hj)
  obtain ⟨X, hX, hn, hmove⟩ := reflected_prime_escape f hf A₀ d.U hA₀ d.U_cyclic d.s d.w
    hsA₀ d.w_not_mem_U d.w_involution d.w_inverts_U d.centralizer_eq hr hro hrU M hrM
  have hmap : A₀.map f = A := map_comap_eq_self hAf
  rw [hmap] at hn hmove
  exact ⟨r, hr, hro, X, hX, hn, hmove⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry

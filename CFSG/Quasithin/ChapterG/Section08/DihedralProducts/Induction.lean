module

public import CFSG.Quasithin.ChapterG.Section08.DihedralProducts.Embedding
public import CFSG.Quasithin.ChapterG.Section08.DihedralProducts.Involution
public import CFSG.Quasithin.ChapterG.Section08.DihedralProducts.Splitting

/-!
# Thompson's dihedral product theorem and its relative form

Induct on the elementary actor's rank, using the complementary commuting
faithful actions from `Splitting`. The rank-one construction supplies a genuine
dihedral embedding. Trivial centers make multiplication of the two embedded
products injective. Prime divisors are retained throughout the induction.

The relative form applies this construction to the kernel on an invariant
subgroup and a faithful complement. It includes rank-zero boundary cases,
which are needed when the prescribed-prime action is already faithful.

Source: Aschbacher–Smith G.8.6–7, printed p.350. The final sentence of G.8.7
uses the dihedral extraction G.8.6, despite citing G.8.5 in print. These results
are conditional only on the universal G.8.2 theorem, as indicated in their names
and arguments; the Section 08 assembly discharges that premise.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section08
variable {G : Type*} [Group G] [Finite G]

/-- Thompson extraction, including rank zero and retaining the prime divisors
of the actual odd subgroup. G.8.2 is the only conditional input. -/
theorem dihedral_extraction (hComplement : FaithfulComplementTheorem G)
    (A X : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (n : ℕ) (hcard : Nat.card A = 2 ^ n) :
    ∃ D : DihedralProduct G n,
      A ≤ D.embedding.range ∧ D.embedding.range ≤ X ⊔ A ∧
      ∀ i, D.prime i ∣ Nat.card X := by
  induction n generalizing A X with
  | zero =>
    have hAbot : A = ⊥ := A.eq_bot_of_card_eq (by simpa using hcard)
    let D : DihedralProduct G 0 :=
      { prime := Fin.elim0
        prime_isPrime := fun i => Fin.elim0 i
        prime_odd := fun i => Fin.elim0 i
        embedding := 1
        injective := fun _ _ _ => Subsingleton.elim _ _ }
    refine ⟨D, ?_, ?_, fun i => Fin.elim0 i⟩
    · rw [hAbot]
      exact bot_le
    · rintro x ⟨y, rfl⟩
      exact one_mem _
  | succ n ih =>
    obtain ⟨B, C, Y, Z, hBA, hCA, hBC, hBcard, hCcard, hYX, hZX,
      hBY, hCZ, hBfaith, hCfaith, hcomm⟩ :=
      dihedral_induction_split hComplement A X hA hX hodd hnorm hfaith n hcard
    let _ := hA
    obtain ⟨D, hBD, hDr, hDp⟩ := ih B Y (dihedral_elementary_le hBA)
      (dihedral_nilpotent_le hX hYX) (hodd.of_dvd_nat (card_dvd_of_le hYX))
      hBY hBfaith hBcard
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by rw [hCcard])
    have haord : orderOf (a : G) = 2 := by simpa using ha
    have ha2 : (a : G) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (haord ▸ dvd_rfl)
    have haneq : (a : G) ≠ 1 := by
      intro he
      simp only [he, orderOf_one] at haord
      omega
    have hCa : zpowers (a : G) = C :=
      eq_of_le_of_card_ge (zpowers_le.mpr a.property)
        (by rw [Nat.card_zpowers, haord, hCcard])
    have hanot : (a : G) ∉ centralizer (Z : Set G) :=
      fun h => haneq (hCfaith.le ⟨a.property, h⟩)
    obtain ⟨E, hCE, hEr, hEp⟩ := exists_dihedral_involution Z
      (hodd.of_dvd_nat (card_dvd_of_le hZX)) a ha2 (hCZ a.property) hanot
    rw [hCa] at hCE hEr
    obtain ⟨F, hFr, hFp⟩ := D.exists_join E
      (hDr.trans (hcomm.trans (centralizer_le hEr)))
    refine ⟨F, ?_, ?_, ?_⟩
    · rw [hFr, ← hBC]
      exact sup_le_sup hBD hCE
    · rw [hFr]
      exact sup_le (hDr.trans (sup_le_sup hYX hBA)) (hEr.trans (sup_le_sup hZX hCA))
    · intro i
      rw [hFp]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using (hDp j).trans (card_dvd_of_le hYX)
      · simpa only [Fin.append_right] using (hEp j).trans (card_dvd_of_le hZX)

/-- The positive-rank source statement G.8.6, conditional on the explicit
G.8.2 input. The witness is an injective homomorphism of concrete groups. -/
theorem lemma_G_8_6_of_faithfulComplement
    (hComplement : FaithfulComplementTheorem G)
    (A X : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (n : ℕ) (_hn : 0 < n) (hcard : Nat.card A = 2 ^ n) :
    ∃ D : DihedralProduct G n, A ≤ D.embedding.range ∧ D.embedding.range ≤ X ⊔ A := by
  obtain ⟨D, hAD, hDX, _⟩ := dihedral_extraction hComplement A X hA hX hodd hnorm hfaith n hcard
  exact ⟨D, hAD, hDX⟩


/-- Relative Thompson extraction. The two products centralize one another,
and their prime lists divide the orders of the respective odd subgroups.
This includes the boundary cases of the source G.8.7. -/
theorem relative_dihedral_extraction (hComplement : FaithfulComplementTheorem G)
    (A X Y B : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (hYX : Y ≤ X) (hAY : A ≤ normalizer (Y : Set G))
    (hB : B = A ⊓ centralizer (Y : Set G))
    (n m : ℕ) (hcard : Nat.card A = 2 ^ n) (hBcard : Nat.card B = 2 ^ m)
    (hmn : m ≤ n) :
    ∃ (D : Subgroup G) (L : DihedralProduct G m) (R : DihedralProduct G (n - m)),
      B ⊓ D = ⊥ ∧ B ⊔ D = A ∧
      B ≤ L.embedding.range ∧
      L.embedding.range ≤ (X ⊓ centralizer ((D ⊔ Y : Subgroup G) : Set G)) ⊔ B ∧
      D ≤ R.embedding.range ∧ R.embedding.range ≤ Y ⊔ D ∧
      L.embedding.range ≤ centralizer (R.embedding.range : Set G) ∧
      (∀ i, L.prime i ∣ Nat.card X) ∧ (∀ i, R.prime i ∣ Nat.card Y) := by
  let _ := hA
  have hBA : B ≤ A := by rw [hB]; exact inf_le_left
  have hBY : B ≤ centralizer (Y : Set G) := by rw [hB]; exact inf_le_right
  have hBfaith : B ⊓ centralizer (X : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hBA).trans hfaith.le)
  obtain ⟨D, hdis, hsup, hBZfaith⟩ := relative_faithful_complement hComplement
    A B X Y hA hX hodd hnorm hBA hYX hAY hBY hBfaith
  have hDA : D ≤ A := hsup ▸ le_sup_right
  have hDcard : Nat.card D = 2 ^ (n - m) := by
    have hc := card_sup_eq_mul_of_normalizes_of_disjoint B D
      (hDA.trans (dihedral_normalizes_subgroup hBA)) (disjoint_iff.mpr hdis)
    rw [hsup, hcard, hBcard] at hc
    have hp : 2 ^ n = 2 ^ m * 2 ^ (n - m) := by
      rw [← pow_add]
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (hc.symm.trans hp)
  have hDfaith : D ⊓ centralizer (Y : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    exact hdis.le ⟨hB.symm ▸ (show x ∈ A ⊓ centralizer (Y : Set G) from ⟨hDA hx.1, hx.2⟩), hx.1⟩
  let Z := X ⊓ centralizer ((D ⊔ Y : Subgroup G) : Set G)
  have hZX : Z ≤ X := inf_le_left
  have hAZ : A ≤ normalizer (Z : Set G) :=
    dihedral_fixed_normalizer A X (D ⊔ Y) hnorm
      ((le_inf (dihedral_normalizes_subgroup hDA) hAY).trans
        (normalizer_inf_normalizer_le_normalizer_sup D Y))
  obtain ⟨L, hBL, hLX, hLp⟩ := dihedral_extraction hComplement B Z
    (dihedral_elementary_le hBA) (dihedral_nilpotent_le hX hZX)
    (hodd.of_dvd_nat (card_dvd_of_le hZX)) (hBA.trans hAZ) hBZfaith m hBcard
  obtain ⟨R, hDR, hRY, hRp⟩ := dihedral_extraction hComplement D Y
    (dihedral_elementary_le hDA) (dihedral_nilpotent_le hX hYX)
    (hodd.of_dvd_nat (card_dvd_of_le hYX)) (hDA.trans hAY) hDfaith (n-m) hDcard
  have hcomm : Z ⊔ B ≤ centralizer ((Y ⊔ D : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · apply le_centralizer_iff.mpr
      exact sup_le ((inf_le_right : Z ≤ centralizer ((D ⊔ Y : Subgroup G) : Set G)).trans
        (centralizer_le (show Y ≤ D ⊔ Y from le_sup_right))) hBY
    · apply le_centralizer_iff.mpr
      exact sup_le ((inf_le_right : Z ≤ centralizer ((D ⊔ Y : Subgroup G) : Set G)).trans
        (centralizer_le (show D ≤ D ⊔ Y from le_sup_left)))
        (hBA.trans (A.le_centralizer.trans (centralizer_le hDA)))
  exact ⟨D, L, R, hdis, hsup, hBL, hLX, hDR, hRY,
    hLX.trans (hcomm.trans (centralizer_le hRY)),
    fun i => (hLp i).trans (card_dvd_of_le hZX), hRp⟩

end CFSG.Quasithin.ChapterG.Section08

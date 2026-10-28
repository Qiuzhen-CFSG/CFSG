module

public import CFSG.Quasithin.ChapterG.Section08.DihedralProducts.Induction

/-!
# A prescribed prime in Thompson's dihedral product

For any A-invariant p-subgroup Y of X on which A acts nontrivially, split A
into its kernel on Y and a faithful complement. The relative extraction gives
a nonempty product whose factor primes divide |Y|, so those primes equal p.
Join this product to the kernel's product and reindex to put a p-factor first.

Specializing Y to the ambient image of O_p(X) proves Aschbacher–Smith G.8.8,
printed p.350, with G.8.2 as the sole conditional input. All primes still divide
|X|. No order or structural statement about O_p(G) is substituted for O_p(X).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section08
variable {G : Type*} [Group G] [Finite G]

/-- Prescribe a factor prime using any invariant p-subgroup on which the
actor is nontrivial. All remaining factors still divide the order of X. -/
theorem dihedral_extraction_prescribed (hComplement : FaithfulComplementTheorem G)
    (A X Y : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (p : ℕ) (hp : p.Prime) (hY : IsPGroup p Y)
    (hYX : Y ≤ X) (hAY : A ≤ normalizer (Y : Set G))
    (hnon : ¬ A ≤ centralizer (Y : Set G))
    (n : ℕ) (hcard : Nat.card A = 2 ^ n) :
    ∃ D : DihedralProduct G n,
      A ≤ D.embedding.range ∧ D.embedding.range ≤ X ⊔ A ∧
      (∀ i, D.prime i ∣ Nat.card X) ∧ ∃ i, D.prime i = p := by
  let _ := hA
  let : Fact p.Prime := ⟨hp⟩
  let B := A ⊓ centralizer (Y : Set G)
  let _ : IsElementaryAbelian 2 B := dihedral_elementary_le inf_le_left
  obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
  have hBA : B < A := lt_of_le_of_ne inf_le_left (by
    intro he
    exact hnon (he ▸ (inf_le_right : B ≤ centralizer (Y : Set G))))
  have hltcard : Nat.card B < Nat.card A :=
    lt_of_le_of_ne (card_le_of_le hBA.le)
      (fun h => hBA.ne (eq_of_le_of_card_ge hBA.le h.ge))
  have hmn : m < n := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    (by simpa only [hm, hcard] using hltcard)
  obtain ⟨D, L, R, hdis, hsup, hBL, hLr, hDR, hRr, hcomm, hLp, hRp⟩ :=
    relative_dihedral_extraction hComplement A X Y B hA hX hodd hnorm hfaith
      hYX hAY rfl n m hcard hm hmn.le
  obtain ⟨F, hFr, hFp⟩ := L.exists_join R hcomm
  have hsum : m + (n - m) = n := by omega
  have hRprime : ∀ i, R.prime i = p := by
    intro i
    obtain ⟨k, hk⟩ := hY.exists_card_eq
    have hd : R.prime i ∣ p :=
      (R.prime_isPrime i).dvd_of_dvd_pow (hk ▸ hRp i)
    exact ((Nat.dvd_prime hp).mp hd).resolve_left (R.prime_isPrime i).ne_one
  have hDA : D ≤ A := hsup ▸ le_sup_right
  have hFbelow : F.embedding.range ≤ X ⊔ A := by
    rw [hFr]
    apply sup_le
    · exact hLr.trans (sup_le_sup inf_le_left hBA.le)
    · exact hRr.trans (sup_le_sup hYX hDA)
  have hFabove : A ≤ F.embedding.range := by
    rw [hFr, ← hsup]
    exact sup_le_sup hBL hDR
  have hFdiv : ∀ i, F.prime i ∣ Nat.card X := by
    intro i
    rw [hFp]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hLp j
    · simpa using (hRp j).trans (card_dvd_of_le hYX)
  have hFselected : ∃ i, F.prime i = p := by
    let j : Fin (n-m) := ⟨0, by omega⟩
    refine ⟨Fin.natAdd m j, ?_⟩
    rw [hFp, Fin.append_right, hRprime]
  have hex : ∃ F : DihedralProduct G (m + (n - m)),
      A ≤ F.embedding.range ∧ F.embedding.range ≤ X ⊔ A ∧
      (∀ i, F.prime i ∣ Nat.card X) ∧ ∃ i, F.prime i = p :=
    ⟨F, hFabove, hFbelow, hFdiv, hFselected⟩
  exact Eq.mp (congrArg (fun t => ∃ F : DihedralProduct G t,
    A ≤ F.embedding.range ∧ F.embedding.range ≤ X ⊔ A ∧
      (∀ i, F.prime i ∣ Nat.card X) ∧ ∃ i, F.prime i = p) hsum) hex

omit [Finite G] in
/-- Place a selected factor first while preserving the embedding range. -/
theorem DihedralProduct.exists_first_prime {n p : ℕ} (D : DihedralProduct G n)
    (hp : ∃ i, D.prime i = p) :
    ∃ (hn : 0 < n) (E : DihedralProduct G n),
      E.embedding.range = D.embedding.range ∧ E.prime ⟨0, hn⟩ = p ∧
      ∀ i, ∃ j, E.prime i = D.prime j := by
  classical
  obtain ⟨i, hi⟩ := hp
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  let z : Fin n := ⟨0, hn⟩
  let e := Equiv.swap z i
  obtain ⟨E, hr, hp⟩ := D.exists_reindex e
  refine ⟨hn, E, hr, ?_, fun j => ⟨e j, hp j⟩⟩
  rw [hp]
  simpa [e, z] using hi

/-- G.8.8 with the actual ambient image of O_p(X), not O_p(G).
The nontrivial action supplies both a positive rank and the prescribed first prime. -/
theorem lemma_G_8_8_of_faithfulComplement
    (hComplement : FaithfulComplementTheorem G)
    (A X : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (p : ℕ) (hp : p.Prime)
    (hnon : ¬ A ≤ centralizer ((pCore p X).map X.subtype : Set G))
    (n : ℕ) (hcard : Nat.card A = 2 ^ n) :
    ∃ (hn : 0 < n) (D : DihedralProduct G n),
      A ≤ D.embedding.range ∧ D.embedding.range ≤ X ⊔ A ∧
      D.prime ⟨0, hn⟩ = p ∧ ∀ i, D.prime i ∣ Nat.card X := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, hAD, hDX, hDp, hi⟩ := dihedral_extraction_prescribed hComplement
    A X ((pCore p X).map X.subtype) hA hX hodd hnorm hfaith p hp
    (pCore_isPGroup.map X.subtype) (map_subtype_le _)
    (hnorm.trans (normalizer_le_normalizer_characteristic_image X (pCore p X)))
    hnon n hcard
  obtain ⟨hn, E, hr, hp, hE⟩ := D.exists_first_prime hi
  refine ⟨hn, E, hr.symm ▸ hAD, hr.symm ▸ hDX, hp, ?_⟩
  intro i
  obtain ⟨j, hj⟩ := hE i
  rw [hj]
  exact hDp j

end CFSG.Quasithin.ChapterG.Section08

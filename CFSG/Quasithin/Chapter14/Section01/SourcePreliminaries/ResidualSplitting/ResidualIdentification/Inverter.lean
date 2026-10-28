module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.NormNum

/-!
# An inverter in a prescribed Sylow two-subgroup

For a finite two-kernel extension of S₃, a Sylow three-subgroup maps faithfully
to A₃. Frattini's argument in the preimage of A₃ makes its normalizer map onto
S₃. A Sylow two-subgroup of that normalizer contains an element mapping to a
transposition, which inverts the three-subgroup by faithfulness. Sylow
conjugacy moves this inverter into the prescribed Sylow two-subgroup.

This is the lifting step in Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), printed p.981, Lemma 14.1.18.
The inverter is not assumed to have order two in the extension.
-/

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries

private theorem three_sylow_image
    {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (P : Sylow 3 G) : (P : Subgroup G).map f = alternatingGroup (Fin 3) := by
  have ha : IsPGroup 3 (alternatingGroup (Fin 3)) := IsPGroup.of_card (n := 1) (by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
  let A : Sylow 3 (Equiv.Perm (Fin 3)) := ha.toSylow (by
    rw [alternatingGroup.index_eq_two]; decide)
  have hnormal : (A : Subgroup (Equiv.Perm (Fin 3))).Normal := inferInstanceAs
    (alternatingGroup (Fin 3)).Normal
  let _ := Sylow.unique_of_normal A hnormal
  exact congrArg (fun S : Sylow 3 (Equiv.Perm (Fin 3)) => (S : Subgroup (Equiv.Perm (Fin 3))))
    (Subsingleton.elim (P.mapSurjective hf) A)

private theorem three_sylow_injective
    {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hker : IsPGroup 2 f.ker)
    (P : Sylow 3 G) : Function.Injective (f.domRestrict (P : Subgroup G)) := by
  have hd := IsPGroup.disjoint_of_ne 3 2 (by decide) (P : Subgroup G) f.ker P.isPGroup' hker
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm ?_ bot_le
  intro x hx
  exact Subtype.ext (Subgroup.disjoint_def.mp hd x.property hx)

private theorem three_normalizer_surjective
    {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (P : Sylow 3 G) :
    Function.Surjective (f.domRestrict (normalizer (P : Set G))) := by
  let F := (alternatingGroup (Fin 3)).comap f
  have hPF : (P : Subgroup G) ≤ F := by
    rw [← map_le_iff_le_comap, three_sylow_image f hf P]
  have hF : F = (P : Subgroup G) ⊔ f.ker := by
    rw [← Subgroup.comap_map_eq, three_sylow_image f hf P]
  have hsup := P.normalizer_sup_eq_top' hPF
  have hPL : (P : Subgroup G) ≤ normalizer (P : Set G) := (P : Subgroup G).le_normalizer
  rw [hF, ← sup_assoc, sup_of_le_left hPL] at hsup
  have hm := congrArg (Subgroup.map f) hsup
  rw [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq, map_top_of_surjective f hf] at hm
  exact MonoidHom.range_eq_top.mp (by simpa only [MonoidHom.domRestrict_range] using hm)

private theorem sylow_two_perm_card (S : Sylow 2 (Equiv.Perm (Fin 3))) : Nat.card S = 2 := by
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [S.card_eq_multiplicity, hcard]
  have hf6 : Nat.factorization 6 2 = 1 := by
    change Nat.factorization (3 * 2) 2 = 1
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  simp [hf6]

private theorem perm_three_inverts :
    ∀ t y : Equiv.Perm (Fin 3), t ^ 2 = 1 → t ≠ 1 → y ^ 3 = 1 → y ≠ 1 →
      t * y * t⁻¹ = y⁻¹ := by decide +kernel

/-- A Sylow two-subgroup in a two-kernel extension of S₃ contains an inverter
of an element of order three. The inverter need not be an involution. -/
public theorem sylow_two_inverted_three_lift
    {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (D : Sylow 2 G) :
    ∃ r ∈ (D : Subgroup G), ∃ y : G,
      orderOf y = 3 ∧ orderOf (f y) = 3 ∧ r * y * r⁻¹ = y⁻¹ := by
  classical
  let P : Sylow 3 G := default
  let L := normalizer (P : Set G)
  let g := f.domRestrict L
  have hg : Function.Surjective g := three_normalizer_surjective f hf P
  let T : Sylow 2 L := default
  let R := T.mapSurjective hg
  have hRcard : Nat.card R = 2 := sylow_two_perm_card R
  have hRne : (R : Subgroup (Equiv.Perm (Fin 3))) ≠ ⊥ := by
    intro he
    have hc := card_eq_one.mpr he
    change Nat.card R = 1 at hc
    omega
  obtain ⟨⟨t, ht⟩, htne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
  have htne : t ≠ 1 := fun he => htne' (Subtype.ext he)
  obtain ⟨u, hu, hut⟩ := Subgroup.mem_map.mp ht
  change f (u : G) = t at hut
  have hftne : f (u : G) ≠ 1 := fun he => htne (hut.symm.trans he)
  have hft2 : f (u : G) ^ 2 = 1 := by
    have htdiv : orderOf t ∣ 2 := hRcard ▸ (R : Subgroup (Equiv.Perm (Fin 3))).orderOf_dvd_natCard ht
    simpa only [← hut] using (orderOf_dvd_iff_pow_eq_one.mp htdiv)
  have hinj := three_sylow_injective f hker P
  have hPcard : Nat.card P = 3 := by
    have hc := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.domRestrict_range, three_sylow_image f hf P, nat_card_alternatingGroup] at hc
    norm_num at hc
    exact hc
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hPcard]; decide)
  obtain ⟨y, hyne⟩ := exists_ne (1 : P)
  have hy : orderOf y = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (hPcard ▸ orderOf_dvd_natCard y) with he | he
    · exact (hyne (orderOf_eq_one_iff.mp he)).elim
    · exact he
  have hyG : orderOf (y : G) = 3 := (orderOf_injective (P : Subgroup G).subtype Subtype.val_injective y).trans hy
  have hyf : orderOf (f (y : G)) = 3 := (orderOf_injective _ hinj y).trans hy
  have hconj : (u : G) * (y : G) * (u : G)⁻¹ ∈ (P : Subgroup G) :=
    (mem_normalizer_iff.mp u.property _).mp y.property
  have hinv : (u : G) * (y : G) * (u : G)⁻¹ = (y : G)⁻¹ := by
    have he : (⟨_, hconj⟩ : P) = y⁻¹ := hinj (by
      change f ((u : G) * (y : G) * (u : G)⁻¹) = f ((y : G)⁻¹)
      simpa only [map_mul, map_inv] using perm_three_inverts (f u) (f y) hft2 hftne
        (by simpa only [hyf] using pow_orderOf_eq_one (f (y : G))) (by intro he; simp [he] at hyf))
    exact congrArg (fun z : P => (z : G)) he
  obtain ⟨S, hTS⟩ := (T.isPGroup'.map L.subtype).exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G S D
  let e := MulAut.conj a
  refine ⟨e (u : G), ?_, e (y : G), ?_, ?_, ?_⟩
  · have huS : (u : G) ∈ (S : Subgroup G) := hTS (mem_map_of_mem L.subtype hu)
    have hh : e (u : G) ∈ (a • S : Sylow 2 G) := by
      change e (u : G) ∈ (S : Subgroup G).map e.toMonoidHom
      exact mem_map_of_mem e.toMonoidHom huS
    rwa [ha] at hh
  · exact (orderOf_injective e.toMonoidHom e.injective _).trans hyG
  · change orderOf (f (a * (y : G) * a⁻¹)) = 3
    rw [map_mul, map_mul, map_inv]
    exact (orderOf_injective (MulAut.conj (f a)).toMonoidHom
      (MulAut.conj (f a)).injective (f y)).trans hyf
  · simpa only [map_mul, map_inv] using congrArg e hinv

end CFSG.Quasithin.Chapter14.SourcePreliminaries

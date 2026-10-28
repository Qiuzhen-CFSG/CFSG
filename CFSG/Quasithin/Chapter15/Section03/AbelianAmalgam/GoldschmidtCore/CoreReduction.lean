module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Basic
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SylowNormalizedSupIndex


/-!
# The three-prime core and the last Thompson reduction

Work inside the finite group that will be `G₀`, so that its two-core is
normal in this ambient group. The intrinsic two-core of `P = O_{3'}(G₀)`
embeds as `O₂(G₀)`. A two-group centralizer of the module eliminates the
odd core of `P`. The precise Sylow output of F.6.11(1) then constructs
`O₂(G₀)J` as a Sylow subgroup of `X = JP`, for `J = J(T_E)`.

To restrict a Thompson factorization of `X` to `P`, its centralizer
factor is a normal two-subgroup: it is a three-prime subgroup of the
{2,3}-group `C_G(F)`. Hence it lies in `O₂(G₀)J`. Removing the `J` part,
which centralizes `F`, gives the literal product `P = C_P(F)N_P(J)`.
Both factors are two-groups by the same prime-support argument, so
F.6.11(1)'s normal Sylow subgroup contains them and `P = O₂(G₀)`.

This module does not assume factorization of `P`. Its extension
factorization, `F ≤ Z₀`, and invariance of `Z₀` remain inputs to be proved
by the application of B.2.14 and B.2.16. Thus the final exported reduction
is not yet the assembled source lemma. All subgroup and centralizer
arguments here apply inside `G₀`; transporting them from the original
ambient group is part of that assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 15.3.68(5), printed pp.1154–1155, PDF pp.1171–1172.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
variable {G : Type*} [Group G] [Finite G]

private theorem twoCore_le_threePrimeCore : pCore 2 G ≤ pPrimeCore 3 G := by
  have hc : Nat.Coprime 3 (Nat.card (pCore 2 G)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact le_sSup ⟨inferInstance, hc⟩

/-- The intrinsic two-core of `O_{3'}(G)` maps to `O₂(G)`. The normality
needed here is inside `G`, which will be the source group `G₀`. -/
theorem twoCore_threePrimeCore :
    Stellmacher.twoCoreAmbient (pPrimeCore 3 G) = pCore 2 G := by
  apply le_antisymm
  · exact le_sSup ⟨by
      change ((pCore 2 (pPrimeCore 3 G)).map (pPrimeCore 3 G).subtype).Normal
      infer_instance, pCore_isPGroup.map (pPrimeCore 3 G).subtype⟩
  · have hl : (pCore 2 G).subgroupOf (pPrimeCore 3 G) ≤ pCore 2 (pPrimeCore 3 G) :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    intro q hq
    exact mem_map.mpr ⟨⟨q, twoCore_le_threePrimeCore hq⟩, hl hq, rfl⟩

/-- Eliminate the odd core in the actual three-prime core, using the
module-centralizer conclusion of 15.3.67(1). -/
theorem oddCore_threePrimeCore_eq_bot (V R : Subgroup G)
    (hV : V ≤ pCore 2 G) (hC : centralizer (V : Set G) ≤ R)
    (hR : IsPGroup 2 R) : pPrimeCore 2 (pPrimeCore 3 G) = ⊥ := by
  apply oddCore_eq_bot (pPrimeCore 3 G) V R _ hC hR
  rwa [twoCore_threePrimeCore]

/-- The extension `J O_{3'}(G)` is still a three-prime group for every
two-subgroup `J`. This does not assume the desired core equality. -/
theorem threePrime_extension_coprime (J : Subgroup G) (hJ : IsPGroup 2 J) :
    Nat.Coprime 3 (Nat.card (J ⊔ pPrimeCore 3 G : Subgroup G)) := by
  have hJ3 : Nat.Coprime 3 (Nat.card J) := by
    obtain ⟨n, hn⟩ := hJ.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes (pPrimeCore 3 G) J
    (by rw [normalizer_eq_top]; exact le_top)
  have hd : Nat.card (pPrimeCore 3 G ⊔ J : Subgroup G) ∣
      Nat.card (pPrimeCore 3 G) * Nat.card J :=
    ⟨Nat.card (pPrimeCore 3 G ⊓ J : Subgroup G), by simpa only [mul_comm] using hm⟩
  rw [sup_comm]
  exact (pPrimeCore_coprime_card (p := 3) (G := G)).mul_right hJ3 |>.of_dvd_right hd

/-- F.6.11(1)'s Sylow output constructs the Sylow subgroup `O₂(G)J` of
`J O_{3'}(G)`. Only the earlier Sylow assertion inside `O_{3'}(G)` is an input. -/
theorem threePrime_extension_sylow (J : Subgroup G) (hJ : IsPGroup 2 J)
    (hQ : Stellmacher.IsSylowSubgroupIn (pCore 2 G) (pPrimeCore 3 G)) :
    Stellmacher.IsSylowSubgroupIn (pCore 2 G ⊔ J) (J ⊔ pPrimeCore 3 G) := by
  obtain ⟨S, hS⟩ := hQ
  have hp : IsPGroup 2 (pCore 2 G ⊔ J : Subgroup G) :=
    pCore_isPGroup.to_sup_of_normal_left hJ
  have hn : pCore 2 G ⊔ J ≤ normalizer (pPrimeCore 3 G : Set G) := by
    rw [normalizer_eq_top]
    exact le_top
  have h := hp.exists_sylow_sup_of_coprime_index (pPrimeCore 3 G) (pCore 2 G ⊔ J)
    hn (S : Subgroup (pPrimeCore 3 G)) S.not_dvd_index (hS ▸ le_sup_left)
  have heq : pPrimeCore 3 G ⊔ (pCore 2 G ⊔ J) = J ⊔ pPrimeCore 3 G := by
    rw [← sup_assoc, sup_eq_left.mpr twoCore_le_threePrimeCore, sup_comm]
  exact heq ▸ h

private theorem twoGroup_of_threePrime_and_support (A B X : Subgroup G)
    (hAB : A ≤ B) (hAX : A ≤ X) (hX : Nat.Coprime 3 (Nat.card X))
    (hB : ∀ p : ℕ, p.Prime → p ∣ Nat.card B → p = 2 ∨ p = 3) : IsPGroup 2 A := by
  apply IsPGroup.of_card
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro p hp hd
  rcases hB p hp (hd.trans (card_dvd_of_le hAB)) with h2 | h3
  · exact h2
  · subst p
    exact ((Nat.prime_three.coprime_iff_not_dvd.mp hX)
      (hd.trans (card_dvd_of_le hAX))).elim

omit [Finite G] in
private theorem normal_two_subgroup_le_sylow_image (A D X : Subgroup G)
    (hAX : A ≤ X) (hA : IsPGroup 2 A) (hn : (A.subgroupOf X).Normal)
    (hD : Stellmacher.IsSylowSubgroupIn D X) : A ≤ D := by
  obtain ⟨S, hS⟩ := hD
  let : (A.comap X.subtype).Normal := hn
  have hl := (hA.comap_subtype (K := X)).le_sylow_of_normal S
  intro a ha
  rw [← hS]
  exact mem_map.mpr ⟨⟨a, hAX ha⟩, hl ha, rfl⟩

omit [Finite G] in
private theorem two_subgroup_le_normal_sylow_image (A Q P : Subgroup G)
    [Q.Normal] (hAP : A ≤ P) (hA : IsPGroup 2 A)
    (hQ : Stellmacher.IsSylowSubgroupIn Q P) : A ≤ Q := by
  obtain ⟨S, hS⟩ := hQ
  have hSP : (S : Subgroup P) = Q.subgroupOf P := by
    rw [← hS]
    exact (comap_map_eq_self_of_injective P.subtype_injective _).symm
  have hn : (S : Subgroup P).Normal := hSP ▸ inferInstance
  let : (S : Subgroup P).Normal := hn
  have hsup := (hA.comap_subtype (K := P)).to_sup_of_normal_right S.isPGroup'
  have hle : A.subgroupOf P ≤ (S : Subgroup P) :=
    le_sup_left.trans (S.is_maximal' hsup le_sup_right).le
  intro a ha
  rw [← hS]
  exact mem_map.mpr ⟨⟨a, hAP ha⟩, hle ha, rfl⟩

/-- Restrict the Thompson factorization of `X = J P` to `P`. The
centralizer factor is a normal two-subgroup of `X`, hence lies in `QJ`.
Correcting its `J`-part preserves centralization of `F`. -/
theorem normal_subgroup_factorization_from_extension
    (P Q J F Z₀ : Subgroup G) [Q.Normal]
    (hQP : Q ≤ P) (hJF : J ≤ centralizer (F : Set G))
    (hFZ : F ≤ Z₀) (hZX : J ⊔ P ≤ normalizer (Z₀ : Set G))
    (hX3 : Nat.Coprime 3 (Nat.card (J ⊔ P : Subgroup G)))
    (hCF : ∀ p : ℕ, p.Prime → p ∣ Nat.card (centralizer (F : Set G)) →
      p = 2 ∨ p = 3)
    (hSylow : Stellmacher.IsSylowSubgroupIn (Q ⊔ J) (J ⊔ P))
    (hfactor : ((J ⊔ P : Subgroup G) : Set G) =
      (((J ⊔ P : Subgroup G) ⊓ centralizer (Z₀ : Set G)) : Set G) *
      (((J ⊔ P : Subgroup G) ⊓ normalizer (J : Set G)) : Set G)) :
    (P : Set G) = (P ⊓ centralizer (F : Set G) : Set G) *
      (P ⊓ normalizer (J : Set G) : Set G) := by
  let X := J ⊔ P
  let C := X ⊓ centralizer (Z₀ : Set G)
  have hCX : C ≤ X := inf_le_left
  have hCtwo : IsPGroup 2 C := twoGroup_of_threePrime_and_support C
    (centralizer (F : Set G)) X (inf_le_right.trans (centralizer_le hFZ))
      hCX hX3 hCF
  have hCN : X ≤ normalizer (centralizer (Z₀ : Set G) : Set G) :=
    hZX.trans ((normal_subgroupOf_iff_le_normalizer
      (centralizer_le_normalizer (Z₀ : Set G))).mp inferInstance)
  have hCn : (C.subgroupOf X).Normal := by
    have hn := normal_subgroupOf_of_le_normalizer hCN
    have heq : C.subgroupOf X = (centralizer (Z₀ : Set G)).subgroupOf X := by
      ext x
      exact and_iff_right x.property
    exact heq ▸ hn
  have hCD : C ≤ Q ⊔ J := normal_two_subgroup_le_sylow_image C _ X hCX hCtwo hCn hSylow
  have hQJ : ((Q ⊔ J : Subgroup G) : Set G) = (Q : Set G) * (J : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ (by rw [normalizer_eq_top]; exact le_top)
  apply Set.Subset.antisymm
  · intro p hp
    have hpX : p ∈ ((J ⊔ P : Subgroup G) : Set G) := mem_sup_right hp
    rw [hfactor] at hpX
    obtain ⟨c, hc, n, hn, hcn⟩ := hpX
    have hcD : c ∈ ((Q ⊔ J : Subgroup G) : Set G) := hCD hc
    rw [hQJ] at hcD
    obtain ⟨q, hq, j, hj, hqj⟩ := hcD
    change q * j = c at hqj
    change c * n = p at hcn
    have hcF : c ∈ centralizer (F : Set G) := centralizer_le hFZ hc.2
    have hqF : q ∈ centralizer (F : Set G) := by
      have hh := (centralizer (F : Set G)).mul_mem hcF
        ((centralizer (F : Set G)).inv_mem (hJF hj))
      simpa only [← hqj, mul_inv_cancel_right] using hh
    have heq : q * (j * n) = p := by rw [← mul_assoc, hqj, hcn]
    have hjnP : j * n ∈ P := by
      have hh := P.mul_mem (P.inv_mem (hQP hq)) hp
      rwa [← heq, inv_mul_cancel_left] at hh
    exact ⟨q, ⟨hQP hq, hqF⟩, j * n,
      ⟨hjnP, (normalizer (J : Set G)).mul_mem (J.le_normalizer hj) hn.2⟩, heq⟩
  · rintro p ⟨c, hc, n, hn, rfl⟩
    exact P.mul_mem hc.1 hn.1

/-- Prime support turns both factors into two-subgroups of the two-closed
group `P`, so each is contained in its normal Sylow subgroup `Q`. -/
theorem normal_subgroup_eq_sylow_from_extension_factorization
    (P Q J F Z₀ M : Subgroup G) [Q.Normal]
    (hQP : Q ≤ P) (hJF : J ≤ centralizer (F : Set G))
    (hFZ : F ≤ Z₀) (hZX : J ⊔ P ≤ normalizer (Z₀ : Set G))
    (hX3 : Nat.Coprime 3 (Nat.card (J ⊔ P : Subgroup G)))
    (hCF : ∀ p : ℕ, p.Prime → p ∣ Nat.card (centralizer (F : Set G)) →
      p = 2 ∨ p = 3)
    (hM : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3)
    (hJM : normalizer (J : Set G) ≤ M)
    (hSylowP : Stellmacher.IsSylowSubgroupIn Q P)
    (hSylowX : Stellmacher.IsSylowSubgroupIn (Q ⊔ J) (J ⊔ P))
    (hfactor : ((J ⊔ P : Subgroup G) : Set G) =
      (((J ⊔ P : Subgroup G) ⊓ centralizer (Z₀ : Set G)) : Set G) *
      (((J ⊔ P : Subgroup G) ⊓ normalizer (J : Set G)) : Set G)) :
    P = Q := by
  have hfact := normal_subgroup_factorization_from_extension P Q J F Z₀
    hQP hJF hFZ hZX hX3 hCF hSylowX hfactor
  have hC : P ⊓ centralizer (F : Set G) ≤ Q :=
    two_subgroup_le_normal_sylow_image _ Q P inf_le_left
      (twoGroup_of_threePrime_and_support _ (centralizer (F : Set G)) (J ⊔ P)
        inf_le_right (inf_le_left.trans le_sup_right) hX3 hCF) hSylowP
  have hN : P ⊓ normalizer (J : Set G) ≤ Q :=
    two_subgroup_le_normal_sylow_image _ Q P inf_le_left
      (twoGroup_of_threePrime_and_support _ M (J ⊔ P)
        (inf_le_right.trans hJM) (inf_le_left.trans le_sup_right) hX3 hM) hSylowP
  apply le_antisymm _ hQP
  intro p hp
  change p ∈ (P : Set G) at hp
  rw [hfact] at hp
  obtain ⟨c, hc, n, hn, rfl⟩ := hp
  exact Q.mul_mem (hC hc) (hN hn)

/-- The last step of 15.3.68, ready for the Thompson application inside
`G₀`. The factorization of the extension remains an explicit intermediate
premise, to be proved before assembling the source lemma. -/
theorem threePrimeCore_eq_twoCore_from_extension_factorization
    (J F Z₀ M : Subgroup G) (hJ : IsPGroup 2 J)
    (hJF : J ≤ centralizer (F : Set G)) (hFZ : F ≤ Z₀)
    (hZX : J ⊔ pPrimeCore 3 G ≤ normalizer (Z₀ : Set G))
    (hCF : ∀ p : ℕ, p.Prime → p ∣ Nat.card (centralizer (F : Set G)) →
      p = 2 ∨ p = 3)
    (hM : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3)
    (hJM : normalizer (J : Set G) ≤ M)
    (hQ : Stellmacher.IsSylowSubgroupIn (pCore 2 G) (pPrimeCore 3 G))
    (hfactor : ((J ⊔ pPrimeCore 3 G : Subgroup G) : Set G) =
      (((J ⊔ pPrimeCore 3 G : Subgroup G) ⊓ centralizer (Z₀ : Set G)) : Set G) *
      (((J ⊔ pPrimeCore 3 G : Subgroup G) ⊓ normalizer (J : Set G)) : Set G)) :
    pPrimeCore 3 G = pCore 2 G := by
  exact normal_subgroup_eq_sylow_from_extension_factorization
    (pPrimeCore 3 G) (pCore 2 G) J F Z₀ M twoCore_le_threePrimeCore
      hJF hFZ hZX (threePrime_extension_coprime J hJ) hCF hM hJM hQ
      (threePrime_extension_sylow J hJ hQ) hfactor

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore

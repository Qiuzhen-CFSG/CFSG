module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.Projective
public import ABG.ChapterII.Section1.Fusion
public import ABG.ChapterII.Section1.WreathedFusion
public import ABG.ChapterII.Section1.FusionFrame
public import ABG.ChapterII.Section1.WreathedFusionFrame
public import Theory.GroupTheory.PResidual.SubnormalSupplement


/-!
# Normalizing the unitary odd Cartan subgroup

In the unitary case of A.3.15(3), the restricted Sylow subgroup S ∩ D
normalizes B. Normality of D makes the restriction an actual Sylow
subgroup, and the projective Hermitian-form comparison transports its
semidihedral or wreathed presentation from SU₃(q).

The permuting product H = B(S ∩ D) has order divisible only by 2 and p,
where p > 3. In the ABG fusion alternatives, every case without a normal
two-complement has an automizer index six. Relative-index divisibility
excludes those cases. The normal two-complement contains B because its
quotient is a two-group; the product decomposition and its trivial
intersection with S ∩ D then identify it with B.

This supplies normalization for the cyclic-factor position argument. The
proof uses the actual projective model and assumes no invariance of the
supplied SL₂ subgroup K. The noncyclicity and q > 3 parameters are retained
for the factor-position consumer, although this normalization step works
without those two restrictions.

Source: Aschbacher–Smith, A.3.15(3), printed pp.50–51, A.3.21(b),
printed pp.55–56, and the proof of 1.3.4, printed pp.510–511 of
`refs/quasithin.pdf`; Alperin–Brauer–Gorenstein, Chapter II §1,
Propositions 1 and 2, article pp.10–13.
-/

public section

open Subgroup
open scoped Pointwise
open CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
variable {G : Type*} [Group G] [Finite G]

private theorem normalComplement_of_three_not_dvd (P : Sylow 2 G)
    (hshape : Stellmacher.IsSemidihedralGroup P ∨ ABG.IsWreathedGroup P)
    (hthree : ¬ 3 ∣ Nat.card G) : HasNormalPComplement 2 G := by
  have hindex (A C : Subgroup G) : A.relIndex C ≠ 6 := by
    intro he
    apply hthree
    exact (show 3 ∣ 6 by decide).trans
      (he ▸ (A.relIndex_dvd_card C).trans C.card_subgroup_dvd_card)
  rcases hshape with hP | ⟨n, hP⟩
  · obtain ⟨T, Q, hf⟩ := ABG.exists_quasiDihedralFusionFrame P hP
    rcases ABG.quasiDihedral_fusion P T Q hf with h | h | h | h
    · exact (hindex _ _ h.2.2.2.1).elim
    · exact (hindex _ _ h.2.2.2.2.2).elim
    · exact (hindex _ _ h.2.2.2.1).elim
    · exact h.1
  · obtain ⟨U, V, hf⟩ := ABG.exists_wreathedFusionFrame P n hP
    rcases ABG.Wreathed.proposition_two P n U V hf with h | h | h | h
    · exact (hindex _ _ h.2.2.1).elim
    · exact (hindex _ _ h.2.2.2.2).elim
    · exact (hindex _ _ h.2.2.1).elim
    · exact h.1

private theorem isPSU_sylow_shape (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (hmodel : ClassicalGroup.IsPSU G 3 q) (T : Sylow 2 G) :
    Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  obtain ⟨P, ⟨ep⟩⟩ := projectiveUnitary_sylow_equiv J q hcard hconj
    (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  let et : T ≃* P := (e.subgroupMap (T : Subgroup G)).trans ep
  rcases su3_sylow_shape q hq P with hs | ⟨n, hw⟩
  · exact Or.inl (ABG.semidihedral_equiv et.symm hs)
  · exact Or.inr ⟨n, ABG.wreathed_equiv et.symm hw⟩

private theorem sylow_le_normalizer_of_permuting (S : Sylow 2 G)
    (hshape : Stellmacher.IsSemidihedralGroup S ∨ ABG.IsWreathedGroup S)
    (B : Subgroup G) {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hB : IsPGroup p B)
    (hperm : (B : Set G) * (S : Set G) = (S : Set G) * (B : Set G)) :
    (S : Subgroup G) ≤ normalizer B := by
  let H := B ⊔ (S : Subgroup G)
  let A := B.subgroupOf H
  let T := S.subtype (show (S : Subgroup G) ≤ H from le_sup_right)
  have hA : IsPGroup p A := hB.comap_subtype
  have hprod (x : H) : ∃ b ∈ A, ∃ t ∈ (T : Subgroup H), b * t = x := by
    have hx : (x : G) ∈ (B : Set G) * (S : Set G) := by
      change (x : G) ∈ (B : Set G) * ((S : Subgroup G) : Set G)
      rw [← coe_sup_of_set_mul_comm B (S : Subgroup G) hperm]
      exact x.property
    obtain ⟨b, hb, t, ht, he⟩ := hx
    exact ⟨⟨b, mem_sup_left hb⟩, hb, ⟨t, mem_sup_right ht⟩, ht, Subtype.ext he⟩
  have hAT : A.IsComplement' (T : Subgroup H) := by
    apply isComplement'_of_disjoint_and_mul_eq_univ
    · exact IsPGroup.disjoint_of_ne p 2 (by omega) A (T : Subgroup H) hA T.isPGroup'
    · exact Set.eq_univ_iff_forall.mpr hprod
  obtain ⟨a, ha⟩ := hA.exists_card_eq
  obtain ⟨t, ht⟩ := T.isPGroup'.exists_card_eq
  have hthree : ¬ 3 ∣ Nat.card H := by
    rw [← hAT.card_mul_card, ha, ht]
    intro hd
    rcases Nat.prime_three.dvd_mul.mp hd with hd | hd
    · have he : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp
        (Nat.prime_three.dvd_of_dvd_pow hd)
      omega
    · exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hTshape : Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T := by
    let e : T ≃* S := subgroupOfEquivOfLe (show (S : Subgroup G) ≤ H from le_sup_right)
    rcases hshape with hs | ⟨n, hw⟩
    · exact Or.inl (ABG.semidihedral_equiv e.symm hs)
    · exact Or.inr ⟨n, ABG.wreathed_equiv e.symm hw⟩
  obtain ⟨N, hN, hNcop, hQ⟩ := normalComplement_of_three_not_dvd T hTshape hthree
  let _ : N.Normal := hN
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hAN : A ≤ N := by
    apply relIndex_eq_one.mp
    apply Nat.eq_one_of_dvd_coprimes _ (N.relIndex_dvd_index_of_normal A)
      (N.relIndex_dvd_card A)
    change Nat.Coprime (Nat.card (H ⧸ N)) (Nat.card A)
    rw [hn, ha]
    exact Nat.coprime_pow_primes _ _ Nat.prime_two Fact.out (by omega)
  have hNT : Disjoint N (T : Subgroup H) := by
    apply disjoint_of_coprime_natCard
    rw [ht]
    exact hNcop.symm.pow_right t
  have hNA : N = A := by
    apply le_antisymm _ hAN
    intro x hx
    obtain ⟨b, hb, s, hs, rfl⟩ := hprod x
    have hsN : s ∈ N := by
      simpa only [inv_mul_cancel_left] using N.mul_mem (N.inv_mem (hAN hb)) hx
    have hs1 : s = 1 := disjoint_def.mp hNT hsN hs
    simpa only [hs1, mul_one] using hb
  have hnormal : A.Normal := hNA ▸ hN
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
    (show B ≤ H from le_sup_left)).mp hnormal)

private theorem permuting_restrict {J : Type*} [Group J] (B S D : Subgroup J)
    (hBD : B ≤ D)
    (hperm : (B : Set J) * (S : Set J) = (S : Set J) * (B : Set J)) :
    (B.subgroupOf D : Set D) * (S.subgroupOf D : Set D) =
      (S.subgroupOf D : Set D) * (B.subgroupOf D : Set D) := by
  apply Set.Subset.antisymm
  · rintro x ⟨b, hb, s, hs, rfl⟩
    have hx : (b : J) * (s : J) ∈ (S : Set J) * (B : Set J) :=
      hperm ▸ Set.mul_mem_mul hb hs
    obtain ⟨s', hs', b', hb', he⟩ := hx
    change s' * b' = (b : J) * (s : J) at he
    have hsD : s' ∈ D := by
      have hh : s' * b' ∈ D := by rw [he]; exact D.mul_mem b.property s.property
      simpa only [mul_inv_cancel_right] using D.mul_mem hh (D.inv_mem (hBD hb'))
    exact ⟨⟨s', hsD⟩, hs', ⟨b', hBD hb'⟩, hb', Subtype.ext he⟩
  · rintro x ⟨s, hs, b, hb, rfl⟩
    have hx : (s : J) * (b : J) ∈ (B : Set J) * (S : Set J) :=
      hperm.symm ▸ Set.mul_mem_mul hs hb
    obtain ⟨b', hb', s', hs', he⟩ := hx
    change b' * s' = (s : J) * (b : J) at he
    have hsD : s' ∈ D := by
      have hh : b' * s' ∈ D := by rw [he]; exact D.mul_mem s.property b.property
      simpa only [inv_mul_cancel_left] using D.mul_mem (D.inv_mem (hBD hb')) hh
    exact ⟨⟨b', hBD hb'⟩, hb', ⟨s', hsD⟩, hs', Subtype.ext he⟩

variable {J : Type*} [Group J] [Finite J]
/-- The restricted ambient Sylow subgroup normalizes B in the unitary case. -/
theorem caseThree_sylow_intersection_le_normalizer
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .unitary .unitary)
    (_hn : ¬ IsCyclic B) (_hlarge : 3 < q) :
    (S : Subgroup J) ⊓ D ≤ normalizer B := by
  let _ : D.Normal := hA.normal
  let _ : Fact p.Prime := ⟨hA.prime⟩
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal D
  have hperm := permuting_restrict B (S : Subgroup J) D hA.inside hA.permutes
  rw [← hT] at hperm
  have hn := sylow_le_normalizer_of_permuting T
    (isPSU_sylow_shape q hC.odd_characteristic hC.model T)
    (B.subgroupOf D) hA.large hA.p_group.comap_subtype hperm
  rw [hT, ← subgroupOf_normalizer_eq hA.inside] at hn
  intro x hx
  exact hn (show (⟨x, hx.2⟩ : D) ∈ (S : Subgroup J).subgroupOf D from hx.1)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition

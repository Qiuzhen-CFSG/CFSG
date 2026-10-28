module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition.SylowModel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Source
public import ABG.ChapterII.Section1.Fusion
public import ABG.ChapterII.Section1.FusionFrame
public import ABG.ChapterII.Section1.WreathedFusion
public import ABG.ChapterII.Section1.WreathedFusionFrame
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.SubgroupProductCard


/-!
# Normalizing the linear Cartan subgroup

Let T = S ∩ D, where D is the normal PSL₃(q) subgroup. Restriction of the
set equality BS = SB gives BT = TB. Inside D, the group H = BT has order
dividing |B||T|, so its order is prime to three since B is a p-group with
p > 3. The restricted Sylow T is also Sylow in H and retains its actual
semidihedral or wreathed presentation.

Choose the corresponding ABG fusion frame. Every fusion alternative except
the normal-two-complement alternative has an automizer index six, which
would divide |H|. Thus H has a normal two-complement N. The odd-order factor
B lies in N because H/N is a two-group; the product H = BT and N ∩ T = 1
then give N = B. Transporting this relative normality back to the ambient
group proves T ≤ N_J(B).

The Sylow presentation is transported through the actual projective model
by `FactorPosition.SylowModel`. No invariance of the supplied SL₂ subgroup
is required. The public statement retains the hypotheses of the linear
factor-position application, although noncyclicity and q > 3 are not needed
for this normalization step.

Source: Aschbacher–Smith, A.3.15(3), printed pp.50–51, A.3.21(b),
printed pp.55–56, and the proof of 1.3.4, printed pp.510–511 of
`refs/quasithin.pdf`; ABG Chapter II, Section 1, Propositions 1 and 2.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {G : Type*} [Group G] [Finite G]

private theorem normalComplement_of_shape (S : Sylow 2 G)
    (hshape : Stellmacher.IsSemidihedralGroup S ∨ ABG.IsWreathedGroup S)
    (hthree : ¬ 3 ∣ Nat.card G) : HasNormalPComplement 2 G := by
  have hindex (U V : Subgroup G) : U.relIndex V ≠ 6 := by
    intro he
    exact hthree ((by decide : 3 ∣ 6).trans
      (he ▸ (U.relIndex_dvd_card V).trans V.card_subgroup_dvd_card))
  have ha (U : Subgroup G) : ABG.automizerIndex U ≠ 6 := hindex _ _
  have ho (V : Subgroup G) : ABG.outerAutomizerIndex V ≠ 6 := hindex _ _
  rcases hshape with hs | ⟨n, hs⟩
  · obtain ⟨U, V, hf⟩ := ABG.exists_quasiDihedralFusionFrame S hs
    rcases ABG.quasiDihedral_fusion S U V hf with h | h | h | h
    · exact (ha U h.2.2.2.1).elim
    · exact (ho V h.2.2.2.2.2).elim
    · exact (ha U h.2.2.2.1).elim
    · exact h.1
  · obtain ⟨U, V, hf⟩ := ABG.exists_wreathedFusionFrame S n hs
    rcases ABG.Wreathed.proposition_two S n U V hf with h | h | h | h
    · exact (ha U h.2.2.1).elim
    · exact (ho V h.2.2.2.2).elim
    · exact (ha U h.2.2.1).elim
    · exact h.1

private theorem odd_factor_normal (B T : Subgroup G)
    (hB : Nat.Coprime 2 (Nat.card B)) (hT : IsPGroup 2 T)
    (hprod : ∀ x : G, ∃ b ∈ B, ∃ t ∈ T, b * t = x)
    (hc : HasNormalPComplement 2 G) : B.Normal := by
  obtain ⟨N, hN, hNcard, hquot⟩ := hc
  let _ : N.Normal := hN
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hquot
  have hBN : B ≤ N := by
    apply relIndex_eq_one.mp
    apply Nat.eq_one_of_dvd_coprimes (hB.symm.pow_right k)
      (N.relIndex_dvd_card B)
    exact (N.relIndex_dvd_index_of_normal B).trans (hk ▸ dvd_rfl)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hT
  have hNT : Disjoint N T := disjoint_of_coprime_natCard (by
    rw [hj]
    exact hNcard.symm.pow_right j)
  have he : B = N := le_antisymm hBN (by
    intro x hx
    obtain ⟨b, hb, t, ht, rfl⟩ := hprod x
    have htN : t ∈ N := by
      have hm := N.mul_mem (N.inv_mem (hBN hb)) hx
      simpa only [inv_mul_cancel_left] using hm
    have ht1 : t = 1 := disjoint_def.mp hNT htN ht
    simpa only [ht1, mul_one] using hb)
  exact he ▸ hN

private theorem sylow_normalizes_permuting_pGroup (S : Sylow 2 G) (B : Subgroup G)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hB : IsPGroup p B)
    (hc : (B : Set G) * (S : Set G) = (S : Set G) * (B : Set G))
    (hshape : Stellmacher.IsSemidihedralGroup S ∨ ABG.IsWreathedGroup S) :
    (S : Subgroup G) ≤ normalizer B := by
  let H : Subgroup G := B ⊔ (S : Subgroup G)
  have hprod : (H : Set G) = (B : Set G) * ((S : Subgroup G) : Set G) :=
    coe_sup_of_set_mul_comm B S hc
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hB
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hthree : ¬ 3 ∣ Nat.card H := by
    intro hd
    have hd' : 3 ∣ Nat.card B * Nat.card S := by
      have hh := card_set_mul_mul_card_inf B (S : Subgroup G)
      rw [← hprod] at hh
      exact hd.trans ⟨_, hh.symm⟩
    rw [ha, hb] at hd'
    rcases Nat.Prime.dvd_mul Nat.prime_three |>.mp hd' with h | h
    · have h3p := Nat.prime_three.dvd_of_dvd_pow h
      have hEq := (Nat.dvd_prime (Fact.out : p.Prime)).mp h3p
      omega
    · exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  let P : Sylow 2 H := S.subtype le_sup_right
  let e : P ≃* S := subgroupOfEquivOfLe (show (S : Subgroup G) ≤ H from le_sup_right)
  have hP : Stellmacher.IsSemidihedralGroup P ∨ ABG.IsWreathedGroup P := by
    rcases hshape with h | ⟨n, h⟩
    · exact Or.inl (ABG.semidihedral_equiv e.symm h)
    · exact Or.inr ⟨n, ABG.wreathed_equiv e.symm h⟩
  have hn : (B.subgroupOf H).Normal := by
    apply odd_factor_normal (B.subgroupOf H) ((S : Subgroup G).subgroupOf H)
    · rw [Nat.card_congr (subgroupOfEquivOfLe (show B ≤ H from le_sup_left)).toEquiv, ha]
      exact (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime) |>.mpr (by omega)).pow_right a
    · exact S.isPGroup'.comap_subtype
    · intro x
      have hx : (x : G) ∈ (B : Set G) * ((S : Subgroup G) : Set G) := by
        rw [← hprod]
        exact x.property
      obtain ⟨b, hb, t, ht, he⟩ := Set.mem_mul.mp hx
      exact ⟨⟨b, mem_sup_left hb⟩, hb, ⟨t, mem_sup_right ht⟩, ht, Subtype.ext he⟩
    · exact normalComplement_of_shape P hP hthree
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
    (show B ≤ H from le_sup_left)).mp hn)

variable {J : Type*} [Group J] [Finite J]

/-- The Sylow subgroup restricted to the linear component normalizes the odd Cartan subgroup. -/
theorem CaseThree.linear_sylow_inf_le_normalizer
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .linear .linear)
    (_hn : ¬ IsCyclic B) (_hlarge : 3 < q) :
    (S : Subgroup J) ⊓ D ≤ normalizer B := by
  let _ : D.Normal := hA.normal
  let _ : Fact p.Prime := ⟨hA.prime⟩
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal D
  have hc : (B.subgroupOf D : Set D) * ((P : Subgroup D) : Set D) =
      ((P : Subgroup D) : Set D) * (B.subgroupOf D : Set D) := by
    apply Set.image_injective.mpr D.subtype_injective
    rw [Set.image_mul D.subtype, Set.image_mul D.subtype,
      ← coe_map, ← coe_map, map_subgroupOf_eq_of_le hA.inside,
      hP, subgroupOf_map_subtype, mul_inf_assoc B S D hA.inside,
      inf_comm (S : Subgroup J) D, inf_mul_assoc D S B hA.inside]
    simp only [Sylow.coe_coe, hA.permutes, Set.inter_comm]
  have hn := sylow_normalizes_permuting_pGroup P (B.subgroupOf D) hA.large
    hA.p_group.comap_subtype hc (isPSL_sylow_shape hC.odd_characteristic hC.model P)
  have hm := (map_mono hn (f := D.subtype)).trans (le_normalizer_map D.subtype)
  simpa only [hP, subgroupOf_map_subtype, map_subgroupOf_eq_of_le hA.inside] using hm

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan

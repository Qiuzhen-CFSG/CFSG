module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import GorensteinWalter.PSL2PerfectOfCard
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Borel and Cartan restrictions in the swapped-component case

In binary PSL₂ with field order at least four, and in the nondegenerate
Suzuki groups, a solvable subgroup containing a Sylow two-subgroup lies in
its normalizer. The concrete rank-one geometry puts every proper overgroup
there; nonsolvability of the full model supplies properness. Actual model
isomorphisms transport this statement. Projecting a solvable overgroup in
Q × Q onto both factors then proves normalization of its Sylow two-subgroup.

For PSL₂, the standard root–torus decomposition gives the torus index q in
the Borel. An odd p-subgroup fixes a coset of the torus, since p does not
divide q, and is therefore conjugate into that torus. Its order divides
q - 1. Applying this to both projections of A gives |A| dividing (q - 1)²;
nontriviality forces p to divide q - 1. A need not itself split as a product.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.510. The
concrete Borel results are F.1.3(1), printed pp.259–260. The Suzuki geometry
uses the proved Huppert–Blackburn III, XI.3.3 and XI.3.6 model results.
-/

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow

private theorem solvable_lt_top {G : Type*} [Group G]
    (hG : ¬ Group.IsSolvable G) (H : Subgroup G) [Group.IsSolvable H] : H < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  subst H
  exact hG (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := G)).toMonoidHom)
    (Subgroup.topEquiv (G := G)).surjective)

private theorem solvable_overgroup_transport {G K : Type*} [Group G] [Finite G] [Group K]
    (e : G ≃* K)
    (hK : ∀ (S : Sylow 2 K) (H : Subgroup K), Group.IsSolvable H →
      (S : Subgroup K) ≤ H → H ≤ normalizer (S : Set K))
    (S : Sylow 2 G) (H : Subgroup G) [Group.IsSolvable H]
    (hSH : (S : Subgroup G) ≤ H) : H ≤ normalizer (S : Set G) := by
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hTH : (T : Subgroup K) ≤ H.map e.toMonoidHom := Subgroup.map_mono hSH
  have hs : Group.IsSolvable (H.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
  have hn := hK T (H.map e.toMonoidHom) hs hTH
  apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  change H.map e.toMonoidHom ≤ (normalizer ((S : Subgroup G) : Set G)).map e.toMonoidHom
  rw [Subgroup.map_normalizer_eq_of_bijective _ e.bijective]
  exact hn

/-- A solvable overgroup of a Sylow two-subgroup in the nondegenerate binary PSL₂ model lies in its Borel normalizer. -/
public theorem binary_model_solvable_overgroup_le_normalizer {Q : Type*} [Group Q] [Finite Q]
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (S : Sylow 2 Q) (H : Subgroup Q) [Group.IsSolvable H]
    (hSH : (S : Subgroup Q) ≤ H) : H ≤ normalizer (S : Set Q) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  apply solvable_overgroup_transport e ?_ S H hSH
  intro T M hM hTM
  let _ := hM
  have hq : 3 < Nat.card F := by
    rw [hF]
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  let _ := GorensteinWalter.psl2_isPerfect_of_card_gt_three F hq
  exact (ChapterF.Source.rankOneSylowFacts_psl2 F n (by omega) hF T).unique_maximal M hTM
    (solvable_lt_top (Group.IsPerfect.not_isSolvable _) M)

/-- A solvable overgroup of a Sylow two-subgroup in the nondegenerate Suzuki model lies in its Borel normalizer. -/
public theorem suzuki_model_solvable_overgroup_le_normalizer {Q : Type*} [Group Q] [Finite Q]
    {m : ℕ} (hm : 1 ≤ m) (e : Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (S : Sylow 2 Q) (H : Subgroup Q) [Group.IsSolvable H]
    (hSH : (S : Subgroup Q) ≤ H) : H ≤ normalizer (S : Set Q) := by
  apply solvable_overgroup_transport e ?_ S H hSH
  intro T M hM hTM
  let _ := hM
  exact (ChapterF.Source.suzuki_rankOneSylowFacts m T).unique_maximal M hTM
    (solvable_lt_top (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m (by omega)) M)

private theorem sylow_eq_prod {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]
    (S : Sylow 2 (G × K)) :
    (S : Subgroup (G × K)) = ((S : Subgroup _).map (MonoidHom.fst G K)).prod
      ((S : Subgroup _).map (MonoidHom.snd G K)) := by
  let S₁ := S.mapSurjective (show Function.Surjective (MonoidHom.fst G K) from
    fun g => ⟨(g, 1), rfl⟩)
  let S₂ := S.mapSurjective (show Function.Surjective (MonoidHom.snd G K) from
    fun k => ⟨(1, k), rfl⟩)
  change (S : Subgroup _) = (S₁ : Subgroup G).prod (S₂ : Subgroup K)
  apply Eq.symm
  apply S.is_maximal'
  · obtain ⟨a, ha⟩ := S₁.isPGroup'.exists_card_eq
    obtain ⟨b, hb⟩ := S₂.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a + b)
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, ha, hb, pow_add]
  · intro x hx
    exact ⟨mem_map_of_mem _ hx, mem_map_of_mem _ hx⟩

private theorem prod_le_normalizer {Q : Type*} [Group Q] [Finite Q]
    (hQ : ∀ (S : Sylow 2 Q) (H : Subgroup Q), Group.IsSolvable H →
      (S : Subgroup Q) ≤ H → H ≤ normalizer (S : Set Q))
    (S : Sylow 2 (Q × Q)) (A : Subgroup (Q × Q))
    [Group.IsSolvable (A ⊔ (S : Subgroup (Q × Q)) : Subgroup (Q × Q))] :
    A ≤ normalizer (S : Set (Q × Q)) := by
  let H := A ⊔ (S : Subgroup (Q × Q))
  have hn (f : (Q × Q) →* Q) (hf : Function.Surjective f) :
      H.map f ≤ normalizer (((S : Subgroup (Q × Q)).map f) : Set Q) := by
    apply hQ (S.mapSurjective hf) (H.map f)
    · exact Group.isSolvable_of_surjective (f.subgroupMap_surjective H)
    · exact Subgroup.map_mono le_sup_right
  have h₁ := hn (MonoidHom.fst Q Q) (fun q => ⟨(q, 1), rfl⟩)
  have h₂ := hn (MonoidHom.snd Q Q) (fun q => ⟨(1, q), rfl⟩)
  apply le_normalizer_iff.mpr
  intro a ha s hs
  have haH : a ∈ H := (show A ≤ H from le_sup_left) ha
  have hsa := (mem_normalizer_iff.mp (h₁ (mem_map_of_mem _ haH)) s.1).mp
    (mem_map_of_mem (MonoidHom.fst Q Q) hs)
  have hsb := (mem_normalizer_iff.mp (h₂ (mem_map_of_mem _ haH)) s.2).mp
    (mem_map_of_mem (MonoidHom.snd Q Q) hs)
  rw [sylow_eq_prod S]
  exact ⟨hsa, hsb⟩

/-- Solvability of the join implies normalization in the product of two binary PSL₂ factors. -/
public theorem binary_model_prod_le_normalizer {Q : Type*} [Group Q] [Finite Q]
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (S : Sylow 2 (Q × Q)) (A : Subgroup (Q × Q))
    [Group.IsSolvable (A ⊔ (S : Subgroup (Q × Q)) : Subgroup (Q × Q))] :
    A ≤ normalizer (S : Set (Q × Q)) :=
  prod_le_normalizer (fun T H hs hTH => by
    let _ := hs
    exact binary_model_solvable_overgroup_le_normalizer hn hmodel T H hTH) S A

/-- The Suzuki normalization required on p.510, in the stronger form allowing an arbitrary subgroup A. -/
public theorem suzuki_model_prod_le_normalizer {Q : Type*} [Group Q] [Finite Q]
    {m : ℕ} (hm : 1 ≤ m) (e : Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (S : Sylow 2 (Q × Q)) (A : Subgroup (Q × Q))
    [Group.IsSolvable (A ⊔ (S : Subgroup (Q × Q)) : Subgroup (Q × Q))] :
    A ≤ normalizer (S : Set (Q × Q)) :=
  prod_le_normalizer (fun T H hs hTH => by
    let _ := hs
    exact suzuki_model_solvable_overgroup_le_normalizer hm e T H hTH) S A

private theorem p_subgroup_conjugate_le_of_index {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] (A C : Subgroup G) (hA : IsPGroup p A)
    (hC : ¬ p ∣ C.index) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ C := by
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ C) hC
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hfix := hx (⟨a, ha⟩ : A)
  have he : (g : G ⧸ C) = (a * g : G) := hfix.symm
  change g⁻¹ * a * (g⁻¹)⁻¹ ∈ C
  simpa only [inv_inv, mul_assoc] using (QuotientGroup.eq.mp he)

open BenderSuzuki.Converse in
private theorem binary_borel_torus_index (F : Type*) [Field F] [Finite F] [CharP F 2] :
    ((PTorus F).subgroupOf (PBorel F)).index = Nat.card F := by
  have hc : Nat.card (PBorel F) = Nat.card F * (Nat.card F - 1) := by
    rw [← PUnip_sup_PTorus]
    rw [Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint]
    · rw [PUnip_card, PTorus_card, Nat.card_units]
    · rw [← ChapterF.Source.Linear.projectiveSylow_coe]
      change PTorus F ≤ normalizer (ChapterF.Source.Linear.projectiveSylow F : Set (PSL2 F))
      rw [ChapterF.Source.Linear.projectiveSylow_normalizer]
      exact PTorus_le_PBorel
    · exact PUnip_disjoint_PTorus
  have hC : Nat.card ((PTorus F).subgroupOf (PBorel F)) = Nat.card F - 1 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (PTorus_le_PBorel (F := F))).toEquiv,
      PTorus_card, Nat.card_units]
  have hh := ((PTorus F).subgroupOf (PBorel F)).card_mul_index
  rw [hC, hc, mul_comm (Nat.card F)] at hh
  exact Nat.eq_of_mul_eq_mul_left (by
    have : 1 < Nat.card F := Finite.one_lt_card
    omega) hh

open BenderSuzuki.Converse in
private theorem binary_borel_pSubgroup_card_dvd {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] (hF : Nat.card F = 2 ^ n) (hp : Odd p)
    (A : Subgroup (PSL2 F)) (hA : IsPGroup p A) (hAB : A ≤ PBorel F) :
    Nat.card A ∣ 2 ^ n - 1 := by
  let C := (PTorus F).subgroupOf (PBorel F)
  let J := A.subgroupOf (PBorel F)
  have hC : ¬ p ∣ C.index := by
    rw [binary_borel_torus_index, hF]
    exact fun h => (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp
      hp.coprime_two_right ((Fact.out : p.Prime).dvd_of_dvd_pow h)
  obtain ⟨g, hg⟩ := p_subgroup_conjugate_le_of_index J C hA.comap_subtype hC
  have hd := Subgroup.card_dvd_of_le hg
  rw [← Nat.card_congr (J.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv] at hd
  have hJ : Nat.card J = Nat.card A := Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv
  have hCT : Nat.card C = Nat.card (PTorus F) :=
    Nat.card_congr (subgroupOfEquivOfLe (PTorus_le_PBorel (F := F))).toEquiv
  simpa only [hJ, hCT, PTorus_card, Nat.card_units, hF] using hd

/-- An odd p-subgroup of a binary PSL₂ Sylow normalizer has order dividing the actual Cartan order q - 1. -/
public theorem binary_model_normalizer_pSubgroup_card_dvd {Q : Type*} [Group Q] [Finite Q]
    {n p : ℕ} [Fact p.Prime] (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) (hp : Odd p)
    (S : Sylow 2 Q) (A : Subgroup Q) (hA : IsPGroup p A)
    (hAN : A ≤ normalizer (S : Set Q)) : Nat.card A ∣ 2 ^ n - 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let _ : Fintype F := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (BenderSuzuki.Converse.PSL2 F)
    T (ChapterF.Source.Linear.projectiveSylow F)
  let c := e.trans (MulAut.conj g)
  have hST : (S : Subgroup Q).map c.toMonoidHom =
      (ChapterF.Source.Linear.projectiveSylow F : Subgroup (BenderSuzuki.Converse.PSL2 F)) := by
    change (S : Subgroup Q).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact congrArg Sylow.toSubgroup hg
  have hAB : A.map c.toMonoidHom ≤ BenderSuzuki.Converse.PBorel F := by
    have h := Subgroup.map_mono (f := c.toMonoidHom) hAN
    change A.map c.toMonoidHom ≤
      (normalizer ((S : Subgroup Q) : Set Q)).map c.toMonoidHom at h
    rw [Subgroup.map_normalizer_eq_of_bijective _ c.bijective, hST] at h
    exact h.trans_eq (ChapterF.Source.Linear.projectiveSylow_normalizer F)
  have hd := binary_borel_pSubgroup_card_dvd hF hp (A.map c.toMonoidHom) (hA.map _) hAB
  rwa [← Nat.card_congr (A.equivMapOfInjective c.toMonoidHom c.injective).toEquiv] at hd

/-- The binary PSL₂ Borel containment and congruence required on printed p.510. -/
public theorem binary_model_prod_restrictions {Q : Type*} [Group Q] [Finite Q]
    {n p : ℕ} [Fact p.Prime] (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (hp : Odd p) (S : Sylow 2 (Q × Q)) (A : Subgroup (Q × Q))
    (hA : IsPGroup p A) (hne : A ≠ ⊥)
    [Group.IsSolvable (A ⊔ (S : Subgroup (Q × Q)) : Subgroup (Q × Q))] :
    A ≤ normalizer (S : Set (Q × Q)) ∧ Nat.ModEq p (2 ^ n) 1 := by
  have hAN := binary_model_prod_le_normalizer hn hmodel S A
  refine ⟨hAN, ?_⟩
  have hd (f : (Q × Q) →* Q) (hf : Function.Surjective f) :
      Nat.card (A.map f) ∣ 2 ^ n - 1 := by
    apply binary_model_normalizer_pSubgroup_card_dvd hmodel hp (S.mapSurjective hf)
      (A.map f) (hA.map f)
    exact (Subgroup.map_mono hAN).trans (Subgroup.le_normalizer_map f)
  have hdiv : Nat.card A ∣ (2 ^ n - 1) ^ 2 := by
    let A₁ := A.map (MonoidHom.fst Q Q)
    let A₂ := A.map (MonoidHom.snd Q Q)
    have hle : A ≤ A₁.prod A₂ := fun a ha => ⟨mem_map_of_mem _ ha, mem_map_of_mem _ ha⟩
    have h := Subgroup.card_dvd_of_le hle
    rw [Nat.card_congr (Subgroup.prodEquiv A₁ A₂).toEquiv, Nat.card_prod] at h
    rw [pow_two]
    exact h.trans (Nat.mul_dvd_mul
      (hd (MonoidHom.fst Q Q) (fun q => ⟨(q, 1), rfl⟩))
      (hd (MonoidHom.snd Q Q) (fun q => ⟨(1, q), rfl⟩)))
  have hpd : p ∣ Nat.card A := hA.card_eq_or_dvd.resolve_left
    (fun h => hne (Subgroup.card_eq_one.mp h))
  exact ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mpr
    ((Fact.out : p.Prime).dvd_of_dvd_pow (hpd.trans hdiv))).symm

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow

module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.NaturalBlock
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LinearThreePrimeRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.NoNaturalSubmodule
public import Theory.SpecificGroups.SL2.FieldCardinality
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived


/-!
# Recognizing rank-two models containing the actual natural block

For a proper full-Sylow local component which is a centerless natural
SL₂(2^n) block with its full two-core, the linear rank-two family has the
same field as the block: its literal two-core quotient is SL₂ over the
containing field. The binary linear endpoint is too small.

Both symplectic parabolic residuals have nontrivial center, excluding that
family. In either G₂ parabolic residual the SL₂ quotient fixes the field,
but the actual two-core has order q⁵ instead of the natural block's q².
For odd n, order bounds exclude the binary symplectic and G₂ derived groups.
The Tits order forces n = 3, when Lagrange's theorem excludes the factor 7.
Thus the eight genuine rank-two model alternatives reduce to PSL₃ over the
original field, triality, or Ree. The moving-Hall owner retains the latter
two exclusions and the source embedding theorem.

The proofs use actual subgroup and quotient equivalences, including the
full-Sylow local membership after ambient transport. No abstract family tag
or order alone is used to assert a group isomorphism. Existing licensed ATLAS
models and their proved local calculations are reused without additional ports.
Source: Aschbacher–Smith A.3.12, pp.47–48, applied in 10.2.3(4), p.747.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.NaturalRankTwo
variable {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
variable {B : Type*} [Group B] {n : ℕ}

theorem quotient_field_card (h : IsL2EvenBlock B n)
    {F : Type*} [Field F] [Finite F] (e : (B ⧸ pCore 2 B) ≃* SL(2,F)) :
    Nat.card F = 2^n := by
  obtain ⟨E,_,_,hE,_,r,⟨m⟩,_⟩ := h.2.2
  exact (Matrix.SL2.field_card_eq_of_equiv (e.symm.trans m.quotientIso)).trans hE

theorem core_card (h : IsL2EvenBlock B n) (hc : pCore 2 B = blockU B)
    (hz : center B = ⊥) : Nat.card (pCore 2 B) = 2^(2*n) := by
  rw [hc,card_eq_card_quotient_mul_card_subgroup (blockFixed B),h.module_card]
  have hb : blockFixed B = ⊥ := by
    change (center B).subgroupOf (blockU B) = ⊥
    rw [hz,bot_subgroupOf]
  rw [hb,card_bot,mul_one,Nat.mul_comm n 2]

omit [Finite X] in
private theorem map_local (e : G ≃* X) (S : Sylow 2 G) (J : Subgroup G)
    (hl : J ∈ localCComponents S) :
    J.map e.toMonoidHom ∈ localCComponents
      (S.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup X) := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom

omit [Finite G] [Finite X] in
private theorem map_proper (e : G ≃* X) (J : Subgroup G) (h : J ≠ ⊤) :
    J.map e.toMonoidHom ≠ ⊤ := by
  intro he
  apply h
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [map_top_of_surjective e.toMonoidHom e.surjective]
  exact he

omit [Finite G] [Finite X] in
private theorem center_bot (e : G ≃* X) (h : center G = ⊥) : center X = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  have hx : e.symm y ∈ center G := ((centerCongr e).symm ⟨y,hy⟩).property
  have hx1 : e.symm y = 1 := by simpa only [h,mem_bot] using hx
  apply mem_bot.mpr
  exact e.symm.injective (hx1.trans (map_one e.symm).symm)

omit [Finite G] [Finite X] in
private theorem core_card_congr (e : G ≃* X) :
    Nat.card (pCore 2 G) = Nat.card (pCore 2 X) :=
  Nat.card_congr ((e.subgroupMap (pCore 2 G)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 e))).toEquiv

theorem linear_field_card (S : Sylow 2 G) (J : Subgroup G)
    (hl : J ∈ localCComponents S) (hp : J ≠ ⊤)
    (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J) (hz : center J = ⊥)
    {F : Type*} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2^f)
    (hf : 1 ≤ f) (e : G ≃* PSL(3,F)) : Nat.card F = 2^n := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hff : 1 < f := by
    by_contra hf'
    have he : f = 1 := by omega
    have hsmall : Nat.card G = 168 := by
      rw [Nat.card_congr e.toEquiv]
      have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
      rw [hF,he] at hh
      norm_num [Fin.prod_univ_succ] at hh ⊢
      exact hh
    have hle := Nat.card_le_card_of_injective J.subtype J.subtype_injective
    rw [NaturalBlock.card h hc hz,hsmall] at hle
    have ha : 2^6 ≤ 2^(3*n) := Nat.pow_le_pow_right (by decide) (by have := h.1; omega)
    have hb : 4 ≤ 2^n := by
      change 2^2 ≤ 2^n
      exact Nat.pow_le_pow_right (by decide) (by have := h.1; omega)
    have hd : 15 ≤ (2^n)^2-1 := by
      have hs : 16 ≤ (2^n)^2 := by nlinarith
      omega
    have hh := Nat.mul_le_mul ha hd
    norm_num at hh
    omega
  let J' := J.map e.toMonoidHom
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨a⟩ := linear_three_local_core_quotient hF hff S' J'
    (map_local e S J hl) (map_proper e J hp)
  let q := QuotientGroup.congr (pCore 2 J) _ (e.subgroupMap J)
    (pCore_map_iso 2 (e.subgroupMap J))
  exact quotient_field_card h (q.trans a)

theorem symplectic_center_ne_bot {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = 2^f) (hf : 1 < f)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (J : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hl : J ∈ localCComponents S) (hp : J ≠ ⊤) : center J ≠ ⊥ := by
  open Theory.SpecificGroups.SymplecticFour in
  obtain ⟨g,hg⟩ := FiveLocalFF.symplectic_local_placement hF hf S J hl hp
  intro hz
  have hz' := center_bot ((MulAut.conj g).subgroupMap J) hz
  change center (J.map (MulAut.conj g).toMonoidHom) = ⊥ at hz'
  rcases hg with hg | hg
  · rw [hg] at hz'
    have hm := Theory.SpecificGroups.SymplecticFour.pointRadicalElement_central (1 : F)
    rw [hz',mem_bot] at hm
    have hh := congrArg (fun g : Theory.SpecificGroups.SymplecticFour.pointLocal (F := F) =>
      g.val.val (.inl 0) (.inr 0)) hm
    exact one_ne_zero hh
  · rw [hg] at hz'
    exact Theory.SpecificGroups.SymplecticFour.Plane.radical_inf_center_ne_bot
      (by rw [hz',inf_bot_eq])

theorem not_symplectic (S : Sylow 2 G) (J : Subgroup G)
    (hl : J ∈ localCComponents S) (hp : J ≠ ⊤) (hz : center J = ⊥)
    {f : ℕ} (hf : 2 ≤ f) : ¬ ClassicalGroup.IsPSp G 2 (2^f) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  exact symplectic_center_ne_bot hF (by omega)
    (S.mapSurjective (f := a.toMonoidHom) a.surjective) (J.map a.toMonoidHom)
    (map_local a S J hl) (map_proper a J hp) (center_bot (a.subgroupMap J) hz)

theorem g2_local_quotient_and_core {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (S : Sylow 2 (Atlas.G2.Model F))
    (J : Subgroup (Atlas.G2.Model F)) (hl : J ∈ localCComponents S) (hp : J ≠ ⊤) :
    Nonempty ((J ⧸ pCore 2 J) ≃* SL(2,F)) ∧ Nat.card (pCore 2 J) = Nat.card F^5 := by
  obtain ⟨g,hg⟩ := FiveLocalFF.G2.local_placement hF S J hl hp
  let a := (MulAut.conj g).subgroupMap J
  let q := QuotientGroup.congr (pCore 2 J) _ a (pCore_map_iso 2 a)
  have hcard : Nat.card (pCore 2 J) = Nat.card (pCore 2 (J.map (MulAut.conj g).toMonoidHom)) := by
    exact core_card_congr a
  suffices hh : Nonempty (((J.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (J.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)) ∧
      Nat.card (pCore 2 (J.map (MulAut.conj g).toMonoidHom)) = Nat.card F^5 by
    exact ⟨⟨q.trans hh.1.some⟩,hcard.trans hh.2⟩
  open Atlas.G2.LieParabolicSetup in
  rcases hg with hg | hg
  · rw [hg]
    exact ⟨⟨Atlas.G2.LieParabolicSetup.local₁CoreQuotientEquivPSL.trans
      Atlas.G2.LieParabolicSetup.longSLEquivPSL.symm⟩,
      Atlas.G2.LieParabolicSetup.card_local₁_pCore⟩
  · rw [hg]
    exact ⟨⟨Atlas.G2.LieParabolicSetup.local₂CoreQuotientEquivPSL.trans
      Atlas.G2.LieParabolicSetup.longSLEquivPSL.symm⟩,
      Atlas.G2.LieParabolicSetup.card_local₂_pCore⟩

theorem not_g2 (S : Sylow 2 G) (J : Subgroup G)
    (hl : J ∈ localCComponents S) (hp : J ≠ ⊤)
    (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J) (hz : center J = ⊥)
    {f : ℕ} (hf : 2 ≤ f) : ¬ ClassificationModels.IsG2At G (2^f) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hf)
  obtain ⟨⟨a⟩,ha⟩ := g2_local_quotient_and_core hlarge
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) (J.map e.toMonoidHom)
    (map_local e S J hl) (map_proper e J hp)
  let q := QuotientGroup.congr (pCore 2 J) _ (e.subgroupMap J)
    (pCore_map_iso 2 (e.subgroupMap J))
  have he : Nat.card F = 2^n := quotient_field_card h (q.trans a)
  have hk : Nat.card (pCore 2 (J.map e.toMonoidHom)) = Nat.card (pCore 2 J) := by
    exact (core_card_congr (e.subgroupMap J)).symm
  rw [hk,core_card h hc hz,he,← pow_mul] at ha
  have hn := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) ha
  have := h.1
  omega

private theorem card_lower_bound [Finite B] (h : IsL2EvenBlock B n)
    (hc : pCore 2 B = blockU B) (hz : center B = ⊥)
    (k : ℕ) (hk : k ≤ n) : 2^(3*k)*((2^k)^2-1) ≤ Nat.card B := by
  rw [NaturalBlock.card h hc hz]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hk) 2) 1)

private theorem not_small (J : Subgroup G) (h : IsL2EvenBlock J n)
    (hc : pCore 2 J = blockU J) (hz : center J = ⊥) (ho : Odd n)
    (hsmall : Nat.card G ≤ 6048) : False := by
  have hn : 3 ≤ n := by have := h.1; obtain ⟨t,ht⟩ := ho; omega
  have hb := card_lower_bound h hc hz 3 hn
  have hl := Nat.card_le_card_of_injective J.subtype J.subtype_injective
  norm_num at hb
  omega

theorem not_symplectic_derived (J : Subgroup G) (h : IsL2EvenBlock J n)
    (hc : pCore 2 J = blockU J) (hz : center J = ⊥) (ho : Odd n) :
    ¬ Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  rintro ⟨e⟩
  apply not_small J h hc hz ho
  have a := Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
  rw [Nat.card_congr (e.trans a).toEquiv,nat_card_alternatingGroup]
  norm_num

theorem not_g2_derived (J : Subgroup G) (h : IsL2EvenBlock J n)
    (hc : pCore 2 J = blockU J) (hz : center J = ⊥) (ho : Odd n) :
    ¬ Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨e⟩
  apply not_small J h hc hz ho
  rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]

theorem not_tits (J : Subgroup G) (h : IsL2EvenBlock J n)
    (hc : pCore 2 J = blockU J) (hz : center J = ⊥) (ho : Odd n) :
    ¬ Nonempty (G ≃* Tits.ParrottGroup) := by
  rintro ⟨e⟩
  have hcard : Nat.card G = 17971200 :=
    (Nat.card_congr e.toEquiv).trans Tits.parrottGroup_card
  have hn : n = 3 := by
    have hl := Nat.card_le_card_of_injective J.subtype J.subtype_injective
    rw [hcard] at hl
    by_contra hne
    have hn : 5 ≤ n := by have := h.1; obtain ⟨t,ht⟩ := ho; omega
    have hb := card_lower_bound h hc hz 5 hn
    norm_num at hb
    omega
  have hd := card_subgroup_dvd_card J
  rw [NaturalBlock.card h hc hz,hn,hcard] at hd
  norm_num at hd

theorem rank_two_alternatives (S : Sylow 2 G) (J : Subgroup G)
    (hl : J ∈ localCComponents S) (hp : J ≠ ⊤)
    (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J) (hz : center J = ⊥)
    (ho : Odd n)
    (hr : Chapter1.Section02.LocalModels.RankTwoTheoremC (⊤ : Subgroup G)) :
    ClassicalGroup.IsPSL G 3 (2^n) ∨
      (∃ f : ℕ, 1 ≤ f ∧ Triality.Standard.IsTrialityGroupAt (2^f) G) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Chapter1.Section02.LocalModels.IsReeF4At G m) := by
  cases hr with
  | linear f hf iso =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := iso
    let e := (topEquiv (G := G)).symm.trans a
    exact Or.inl ⟨F,inferInstance,inferInstance,
      linear_field_card S J hl hp h hc hz hF hf e,⟨e⟩⟩
  | symplectic f hf iso =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := iso
    exact (not_symplectic S J hl hp hz hf
      ⟨F,inferInstance,inferInstance,hF,⟨(topEquiv (G := G)).symm.trans a⟩⟩).elim
  | g2 f hf iso =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := iso
    exact (not_g2 S J hl hp h hc hz hf
      ⟨F,inferInstance,inferInstance,hF,⟨(topEquiv (G := G)).symm.trans a⟩⟩).elim
  | triality f hf iso =>
    exact Or.inr (Or.inl ⟨f,hf,iso.of_mulEquiv (topEquiv (G := G)).symm⟩)
  | ree m hm iso =>
    obtain ⟨d,⟨e⟩⟩ := iso
    exact Or.inr (Or.inr ⟨m,hm,d,⟨(topEquiv (G := G)).symm.trans e⟩⟩)
  | symplectic_derived iso =>
    exact (not_symplectic_derived J h hc hz ho
      ⟨(topEquiv (G := G)).symm.trans iso.some⟩).elim
  | g2_derived iso =>
    exact (not_g2_derived J h hc hz ho
      ⟨(topEquiv (G := G)).symm.trans iso.some⟩).elim
  | tits iso =>
    exact (not_tits J h hc hz ho
      ⟨(topEquiv (G := G)).symm.trans iso.some⟩).elim

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.NaturalRankTwo

module
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.LinearRecognition
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveOddModels
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThreeParameter
public import GorensteinWalter.SL2UniversalCover
public import Theory.SpecificGroups.OddThreePerfectLifts
public import Theory.SpecificGroups.OddThreeRank
public import Theory.GroupTheory.PerfectRankTwoCoreInvolution

/-!
# The genuine odd ternary A₅ section parameter

A local component with A₅ two-core quotient, normalized by a full Sylow
in odd prime PSL₃ or PSU₃, is the actual SL₂(5) cover. If its two-core is
nontrivial, the ambient two-rank bound supplies an involution centralized
by both the component and the full Sylow. The cubic scalar cover of that
involution centralizer lifts the perfect component faithfully into prime
SL₂. Dickson recognition makes this component quasisimple, so the genuine
central two-cover classification gives A₅ or SL₂(5). Full-Sylow normalization
excludes A₅ and forces the field parameter to be five in the remaining case.

The argument retains the literal local section and never uses a field-five
order bound to identify the prime. Its final theorem is the missing odd
ternary row in the Cartan containing-component sieve.

Source: Aschbacher–Smith A.3.12(9), A.3.14 and A.3.21(a), printed pp.47–50,55,
applied to Proposition 9.3.1, printed pp.732–733.
-/

public noncomputable section
open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]

omit [Finite K] [Group.IsPerfect K] in
private theorem five_dvd_card (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    5 ∣ Nat.card K := by
  have hc : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
    norm_num
  exact (show 5 ∣ 60 by decide).trans (hc ▸ (pCore 2 K).card_quotient_dvd_card)

private theorem quasisimple_of_prime_sl2_embedding
    {F : Type*} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : Nat.card F = p) (i : K →* SL(2,F)) (hi : Function.Injective i)
    (hfive : 5 ∣ Nat.card K) : IsQuasisimple K := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hc, ZMod.card])
  let f := (GorensteinWalter.sl2RingEquiv a).toMonoidHom.comp i
  have hf : Function.Injective f := (GorensteinWalter.sl2RingEquiv a).injective.comp hi
  let e : K ≃* f.range := MonoidHom.ofInjective hf
  have hd : 5 ∣ p * (p ^ 2 - 1) := by
    have h := hfive.trans ((Nat.card_congr e.toEquiv).symm ▸ f.range.card_subgroup_dvd_card)
    simpa only [GorensteinWalter.sl2_card_formula, Nat.card_zmod] using h
  have hlarge : 3 < p := by
    have hp2 := hp.two_le
    have hodd := Nat.odd_iff.mp ho
    by_contra hh
    have he : p = 3 := by omega
    norm_num [he] at hd
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp
    ((by decide : 1 < 5).trans_le (Nat.le_of_dvd Nat.card_pos hfive))
  let : Nontrivial f.range := e.symm.nontrivial
  rcases ChapterA.RankActions.primePerfectSL2Recognition p hlarge f.range
    inferInstance inferInstance with hfull | ⟨_,hfive⟩
  · obtain ⟨b⟩ := hfull
    let : Fact (3 < Nat.card (ZMod p)) := ⟨by simpa using hlarge⟩
    exact IsQuasisimple.of_mulEquiv (e.trans b).symm
  · obtain ⟨b⟩ := hfive
    let : Fact (3 < Nat.card (ZMod 5)) := ⟨by norm_num⟩
    exact IsQuasisimple.of_mulEquiv (e.trans b).symm

private theorem quasisimple_of_cubic_centralizer
    {V H F E : Type*} [Group V] [Group H] [Field F] [Field E] [Finite E]
    (ρ : V →* GL (Fin 2) F) (hρ : Function.Injective ρ)
    (f : V →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center V)
    (h3 : ∀ v ∈ f.ker, v ^ 3 = 1)
    (d : (GeneralLinearGroup.det.comp ρ).ker ≃* SL(2,E))
    (j : K →* H) (hj : Function.Injective j)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hE : Nat.card E = p)
    (hfive : 5 ∣ Nat.card K) : IsQuasisimple K := by
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp
    ((by decide : 1 < 5).trans_le (Nat.le_of_dvd Nat.card_pos hfive))
  let e : K ≃* j.range := MonoidHom.ofInjective hj
  let : Group.IsPerfect j.range := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hn : ¬ IsMulCommutative V := by
    intro ha
    have hh : IsMulCommutative H := IsMulCommutative.of_comm (fun x y => by
      obtain ⟨x,rfl⟩ := hf x
      obtain ⟨y,rfl⟩ := hf y
      rw [←map_mul,←map_mul,ha.is_comm.comm x y])
    exact Group.IsPerfect.not_isMulCommutative K (IsMulCommutative.of_comm
      (fun x y => hj (by rw [map_mul,map_mul,hh.is_comm.comm])))
  let D := (GeneralLinearGroup.det.comp ρ).ker
  let a : D ≃* D.map f := MulEquiv.ofBijective (f.subgroupMap D)
    ⟨Theory.SpecificGroups.OddThreeLevi.determinant_kernel_injective ρ hρ hn f hk h3,
      f.subgroupMap_surjective D⟩
  have hB : j.range ≤ D.map f :=
    Theory.SpecificGroups.OddThreeLevi.perfect_subgroup_le_det_kernel_image ρ f hf j.range
  let i := d.toMonoidHom.comp (a.symm.toMonoidHom.comp
    ((inclusion hB).comp e.toMonoidHom))
  have hi : Function.Injective i := d.injective.comp
    (a.symm.injective.comp ((inclusion_injective hB).comp e.injective))
  exact quasisimple_of_prime_sl2_embedding hp ho hE i hi hfive


private def centralizer_embedding {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (z : G)
    (hz : B ≤ centralizer ({z} : Set G)) :
    B →* centralizer ({e z} : Set H) :=
  (e.toMonoidHom.comp B.subtype).codRestrict _ (by
    intro b
    apply mem_centralizer_singleton_iff.mpr
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      ← map_mul] using congrArg e (mem_centralizer_singleton_iff.mp (hz b.property)))

private theorem centralizer_embedding_injective {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (z : G) (hz : B ≤ centralizer ({z} : Set G)) :
    Function.Injective (centralizer_embedding e B z hz) := by
  intro a b h
  exact Subtype.ext (e.injective (congrArg Subtype.val h))

private theorem section_quasisimple_of_involution
    {G : Type*} [Group G] [Finite G] (B : Subgroup G) [Group.IsPerfect B]
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p)
    (z : G) (hz : orderOf z = 2) (hBz : B ≤ centralizer ({z} : Set G)) :
    IsQuasisimple B := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have h2 := Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho
      (k := 1) (by simpa using hF)
    obtain ⟨f,hf,hk,h3⟩ := PSL3.OddInvolutionFixed.exists_gl2_cubic_central_surjection
      (e z) ((e.orderOf_eq z).trans hz) h2
    exact quasisimple_of_cubic_centralizer (MonoidHom.id _) Function.injective_id
      f hf hk h3 (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm
      (centralizer_embedding e B z hBz) (centralizer_embedding_injective e B z hBz)
      hp ho hF (five_dvd_card eB)
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    obtain ⟨f,hf,hk,h3⟩ := SU3.OddCubicCentralizer.surjection p ho F J hF hc
      (e z) ((e.orderOf_eq z).trans hz)
    let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
    let d : J2.unitaryDet.ker ≃* SL(2,GaloisField p 1) :=
      J2.unitaryDetKernelEquiv.trans (ABG.specialUnitaryTwo_equiv_sl2 p 1 ho one_ne_zero)
    exact quasisimple_of_cubic_centralizer J2.unitarySubgroup.subtype Subtype.val_injective
      f hf hk h3 d (centralizer_embedding e B z hBz)
      (centralizer_embedding_injective e B z hBz) hp ho
      (by simpa using GaloisField.card p 1 one_ne_zero) (five_dvd_card eB)

private theorem odd_three_rank {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p) :
    primeRank 2 G ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_congr 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le hp ho hF
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J hp ho hF hc

/-- The genuine local A₅ two-core section in an odd prime ternary group
is quasisimple and is the actual binary cover SL₂(5). -/
theorem odd_three_five_section_models
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p) :
    IsQuasisimple B ∧ Chapter1.Section02.LocalModels.IsSL B 2 5 := by
  let : Group.IsPerfect B := by
    let := hl.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let : IsQuasisimple B := by
    by_cases hcore : pCore 2 B = ⊥
    · let a : B ≃* (B ⧸ pCore 2 B) :=
        QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcore).symm
      exact IsQuasisimple.of_mulEquiv (a.trans eB).symm
    · obtain ⟨z,_,hz,hBz⟩ := exists_involution_centralized_by_perfect_sup_sylow
        S B (odd_three_rank hp ho hm) hn hcore
      exact section_quasisimple_of_involution B eB hp ho hm z hz (le_sup_left.trans hBz)
  refine ⟨inferInstance,?_⟩
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e4⟩ := ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  have hb : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^2) :=
    ⟨GaloisField 2 2,inferInstance,inferInstance,hc,⟨eB.trans e4.symm⟩⟩
  rcases ChapterC.Section05.NormalizerControl.EmbeddingSelection.quasisimple_binary_core_models
    (by decide : 1 < 2) hb with hsimple | ⟨_,hcover⟩
  · obtain ⟨E,_,_,hE,⟨eE⟩⟩ := hsimple
    obtain ⟨e5⟩ := ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (show Nat.card E = 4 from hE)
    rcases hm with hm | hm
    · exact (AlternatingFive.not_odd_linear S hl hn (eE.trans e5) hp ho hm).elim
    · exact (AlternatingFive.not_odd_unitary S hl hn (eE.trans e5) hp ho hm).elim
  · exact hcover

/-- A full Sylow normalizing the literal local A₅ two-core section forces
parameter five in either odd prime ternary family. -/
theorem odd_three_five_section_parameter
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hsection : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p) : p = 5 := by
  obtain ⟨eB⟩ := hsection
  obtain ⟨hB,hmodel⟩ := odd_three_five_section_models S B hl hn eB hp ho hm
  let : IsQuasisimple B := hB
  rcases hm with hm | hm
  · exact ChapterC.Section05.NormalizerControl.EmbeddingSelection.odd_three_sl2_five_parameter
      S B hmodel hn hp ho false (.inl hm)
  · exact ChapterC.Section05.NormalizerControl.EmbeddingSelection.odd_three_sl2_five_parameter
      S B hmodel hn hp ho true (.inl hm)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings


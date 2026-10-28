module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.BinaryLinear.Source
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.ExceptionalSmall
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115
public import Theory.GroupTheory.Amalgam.LocalStructure
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived


/-!
# Paired deleted alternating-five blocks in the even source models

A literal local C-component of order 960 with two-core quotient A₅ has
its two-core of order16. The rank-two placement theorems force field
order four. The G₂ and triality root radicals then have orders 4⁵ and
4¹¹, which cannot be that core. In PSL₃(4) and PSp₄(4), Lagrange's
theorem excludes the order960² of two disjoint commuting source blocks.
The Bender, higher binary linear, Ree, Tits and small derived rows are
excluded by their existing full-Sylow or two-local results.

The final consumer keeps the original deleted blocks, their full Sylow
marking, their actual cores, and an injective homomorphism of their
product. Passing to an ordinary component's central quotient must supply
these same data there; quotient injectivity is not inferred from the A₅
section alone.

Source: Aschbacher–Smith, 1.2.8(1–2), printed pp.506–507, and its use in
14.6.9 at the residual centralizer normalizer, printed p.1026.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
open CFSG.Quasithin.Chapter1.Section02


namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedEvenPair
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem quotient_card {B : Subgroup G}
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card (B ⧸ pCore 2 B) = 60 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

omit [Finite G] in
private theorem core_card {B : Subgroup G} (hc : Nat.card B = 960)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card (pCore 2 B) = 16 := by
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B), quotient_card e] at hc
  omega

omit [Finite G] in
private theorem proper {B : Subgroup G} (hc : Nat.card B = 960)
    (hpair : 921600 ∣ Nat.card G) : B ≠ ⊤ := by
  intro ht
  rw [ht, Nat.card_congr topEquiv.toEquiv] at hc
  rw [hc] at hpair
  norm_num at hpair

omit [Finite G] in
private theorem core_ne_bot {B : Subgroup G} (hc : Nat.card B = 960)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : pCore 2 B ≠ ⊥ := by
  intro hz
  have hh := core_card hc e
  rw [hz] at hh
  simp at hh

private theorem of_equiv {H : Type*} [Group H] [Finite H]
    (hH : ∀ (S : Sylow 2 H) (B : Subgroup H), B ∈ localCComponents S →
      Nat.card B = 960 → ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) →
      921600 ∣ Nat.card H → False)
    (a : G ≃* H) (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S) (hc : Nat.card B = 960)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hpair : 921600 ∣ Nat.card G) : False := by
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  let d := B.equivMapOfInjective a.toMonoidHom a.injective
  exact hH (S.mapSurjective (f := a.toMonoidHom) a.surjective) (B.map a.toMonoidHom)
    (localCComponents_map_of_solvable_ker hB a.toMonoidHom)
    ((Nat.card_congr d.toEquiv).symm.trans hc)
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans e)
    ((Nat.card_congr a.toEquiv) ▸ hpair)

private theorem not_linear {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hc : Nat.card B = 960)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hpair : 921600 ∣ Nat.card PSL(3,F)) : False := by
  by_cases hn2 : 1 < n
  · obtain ⟨hfour, _⟩ := FiveLocalFF.linear_three_five_section_placement hF hn2
      S B hB (proper hc hpair) e
    rw [Matrix.PSL3.LinearThree.card_projective, hfour] at hpair
    norm_num at hpair
  · have hn1 : n = 1 := by omega
    rw [Matrix.PSL3.LinearThree.card_projective, hF, hn1] at hpair
    norm_num at hpair

private theorem not_symplectic {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (B : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hB : B ∈ localCComponents S) (hc : Nat.card B = 960)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hpair : 921600 ∣ Nat.card (Theory.SpecificGroups.SymplecticFour.Sp F)) : False := by
  obtain ⟨hfour, _⟩ := FiveLocalFF.symplectic_five_section_placement hF (by omega)
    S B hB (proper hc hpair) e
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, hfour] at hpair
  norm_num at hpair

private theorem not_g2 {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (S : Sylow 2 (Atlas.G2.Model F)) (B : Subgroup (Atlas.G2.Model F))
    (hB : B ∈ localCComponents S) (hc : Nat.card B = 960)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hpair : 921600 ∣ Nat.card (Atlas.G2.Model F)) : False := by
  have hgt : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn)
  obtain ⟨hfour, g, hg⟩ := FiveLocalFF.G2.five_section_placement hgt
    S B hB (proper hc hpair) e
  have hcc := LocalCoreTransport.core_card 2 (B.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  rw [core_card hc e] at hcc
  rcases hg with hg | hg
  · rw [hg, Atlas.G2.LieParabolicSetup.card_local₁_pCore, hfour] at hcc
    norm_num at hcc
  · rw [hg, Atlas.G2.LieParabolicSetup.card_local₂_pCore, hfour] at hcc
    norm_num at hcc

private theorem not_triality (n : ℕ) (hn : 0 < n)
    (S : Sylow 2 (Triality.Standard.BinaryCarrier n hn))
    (B : Subgroup (Triality.Standard.BinaryCarrier n hn))
    (hB : B ∈ localCComponents S) (hc : Nat.card B = 960)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (_hpair : 921600 ∣ Nat.card (Triality.Standard.BinaryCarrier n hn)) : False := by
  obtain ⟨hfour, g, hg⟩ := FiveLocalFF.Triality.five_section_placement n hn
    S B hB (core_ne_bot hc e) e
  have hcc := LocalCoreTransport.core_card 2 (B.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  rw [core_card hc e, hg,
    Triality.Standard.Parabolics.localFactor_central_twoCore_card _ rfl] at hcc
  change 16 = (2 ^ n) ^ 11 at hcc
  rw [hfour] at hcc
  norm_num at hcc

/-- The complete characteristic-two rank-two list excludes the actual pair orders. -/
theorem not_rank_two (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S) (hc : Nat.card B = 960)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hpair : 921600 ∣ Nat.card G) (hm : LocalModels.RankTwoTheoremC G) : False := by
  cases hm with
  | linear n hn hm =>
    obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact of_equiv (not_linear hF hn) a S B hB hc e hpair
  | symplectic n hn hm =>
    obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let b := a.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    exact of_equiv (not_symplectic hF hn) b S B hB hc e hpair
  | g2 n hn hm =>
    obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact of_equiv (not_g2 hF hn) a S B hB hc e hpair
  | triality n hn hm =>
    obtain ⟨a⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n (by omega)).mp hm
    exact of_equiv (not_triality n (by omega)) a S B hB hc e hpair
  | ree m hm he =>
    obtain ⟨a⟩ := (ReeF4.exists_localBlockInput_mulEquiv_iff G m).mp he
    exact FiveLocalFF.ExceptionalSmall.not_ree B (core_ne_bot hc e) e hm a
  | symplectic_derived he =>
    let a := he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
    rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup] at hpair
    norm_num at hpair
  | g2_derived he =>
    rw [Nat.card_congr he.some.toEquiv, Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hpair
    norm_num at hpair
  | tits he =>
    exact FiveLocalFF.ExceptionalSmall.not_tits B (core_ne_bot hc e) e he.some

/-- Every even row of 1.1.5 excludes the local order960 block inside an order960² pair. -/
theorem not_lie_type_two [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S) (hc : Nat.card B = 960)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hpair : 921600 ∣ Nat.card G) (hm : LieTypeTwoModel G) : False := by
  rcases hm with hb | hr | ⟨d, hd, hm⟩
  · have ht : (⊤ : Subgroup G).IsCComponent :=
      (show IsComponent G ⊤ from ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
    exact proper hc hpair (eq_of_bender_containing_component S hB ht le_top
      (hb.of_mulEquiv topEquiv))
  · exact not_rank_two S B hB hc e hpair hr
  · exact FiveLocalFF.BinaryLinear.not_section_binary_linear S B hB e hd hm

/-- Source deleted-block consumer retaining its actual two-core and ambient pair order. -/
theorem not_deleted_block [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S) (hblock : ChapterC.IsAlternatingBlock B 5)
    (hcore : Nat.card (pCore 2 B) = 16)
    (hpair : 921600 ∣ Nat.card G) (hm : LieTypeTwoModel G) : False := by
  obtain ⟨e⟩ := hblock.2.2.quotient_iso
  have hc : Nat.card B = 960 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B), quotient_card e, hcore]
  exact not_lie_type_two S B hB hc e hpair hm

/-- The literal product of two source deleted blocks cannot embed in an even source row. -/
theorem not_deleted_pair [IsQuasisimple G]
    (S : Sylow 2 G) (B C : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hb : ChapterC.IsAlternatingBlock B 5) (hc : ChapterC.IsAlternatingBlock C 5)
    (hbc : Nat.card (pCore 2 B) = 16) (hcc : Nat.card (pCore 2 C) = 16)
    (f : B × C →* G) (hf : Function.Injective f) (hm : LieTypeTwoModel G) : False := by
  apply not_deleted_block S B hB hb hbc _ hm
  have hd := Subgroup.card_dvd_of_injective f hf
  have hbcard : Nat.card B = 960 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),
      quotient_card hb.2.2.quotient_iso.some, hbc]
  have hccard : Nat.card C = 960 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 C),
      quotient_card hc.2.2.quotient_iso.some, hcc]
  simpa only [Nat.card_prod, hbcard, hccard] using hd

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedEvenPair

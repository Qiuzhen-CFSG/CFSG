module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.Sections
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankTwoPerfect
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.AtlasPort.LinearGroups.G2.PerfectSubgroups
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Triality.InvolutionFixedRank
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Theory.SpecificGroups.Tits.FiniteSimple
public import CFSG.Quasithin.MainConverse.ExceptionalLocal
public import CFSG.Quasithin.MainConverse.ReeLocal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms.Full
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure

/-!
# Exceptional local sections in the even rank-two catalogue

A Sylow-normalized local C-component whose intrinsic two-core quotient is
J₂, M₂₃, or PSL₃(4) fills a simple containing group in the Theorem C
rank-two catalogue. Its perfectness and three-rank force the full join in
PSL₃, Sp₄, and G₂. A nontrivial intrinsic core places the triality and Ree
cases in parabolics with incompatible rank or order. When the core vanishes,
even characteristic gives a faithful Sylow action on the exceptional group;
its actual automorphism order has two-part less than 4096, contradicting
the unipotent subgroup in either remaining family. The small rows are
excluded by the divisor 35.

Source: Aschbacher–Smith A.3.12 and its exceptional application in 13.6.27,
printed pp.47–48 and 934. All section equivalences concern the actual carriers.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem cardinal_divisors {B : Subgroup G} (h : IsModel (B ⧸ pCore 2 B)) :
    15 ∣ Nat.card B ∧ 35 ∣ Nat.card B :=
  ⟨(by decide : 15 ∣ 20160).trans (section_card_dvd h),
    (by decide : 35 ∣ 20160).trans (section_card_dvd h)⟩
omit [Finite G] in
private theorem aut_card_not_dvd {B : Subgroup G} (h : IsModel (B ⧸ pCore 2 B))
    (hc : pCore 2 B = ⊥) : ¬ 4096 ∣ Nat.card (MulAut B) := by
 let q : B ≃* B ⧸ pCore 2 B :=
   ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm
 rcases h with h | h | h
 · rw [Nat.card_congr (MulAut.congr (q.trans h.some)).toEquiv,
     ← Nat.card_congr Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionEquivAut.toEquiv,
     Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.card_extension
       Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_l₁]
   decide
 · have hd := card_dvd_of_surjective (MulAut.conj : Sporadic.Mathieu.M23 →* _)
     Sporadic.Mathieu.m23_conj_surjective
   rw [Sporadic.Mathieu.m23_order] at hd
   rw [Nat.card_congr (MulAut.congr (q.trans h.some)).toEquiv]
   exact fun hh => (by decide : ¬ 4096 ∣ 10200960) (hh.trans hd)
 · have hd : Nat.card (MulAut Matrix.PSL3Four.PSL) ∣ 20160 * 12 := by
     rw [← (MulAut.innerSubgroup Matrix.PSL3Four.PSL).card_mul_index]
     apply Nat.mul_dvd_mul
     · simpa only [Matrix.PSL3Four.card_PSL] using
         (card_range_dvd (MulAut.conj : Matrix.PSL3Four.PSL →* _))
     · exact Matrix.PSL3Four.OuterThreeStructure.outer_card_dvd_twelve
   rw [Nat.card_congr (MulAut.congr (q.trans h.some)).toEquiv]
   exact fun hh => (by decide : ¬ 4096 ∣ 20160 * 12) (hh.trans hd)
private theorem not_large_twoPart
    (S : Sylow 2 G) (hE : IsEvenCharacteristicAt S)
    {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) (hc : pCore 2 B = ⊥) :
    ¬ 4096 ∣ Nat.card G := by
 let q : B ⧸ pCore 2 B ≃* B :=
   (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
 let : IsSimpleGroup (B ⧸ pCore 2 B) := h.isSimple
 let : IsSimpleGroup B := q.symm.isSimpleGroup
 let := local_perfect hB
 have hz : center B = ⊥ :=
   (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
     (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
 let : IsQuasisimple B :=
   ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
 have hfaith := sylow_centralizer_eq_bot_of_evenCharacteristic S hE hB hSB
 let f := B.normalizerMonoidHom.comp (inclusion hSB)
 have hf : Function.Injective f := by
   apply (MonoidHom.ker_eq_bot_iff _).mp
   apply eq_bot_iff.mpr
   intro a ha
   apply Subtype.ext
   apply mem_bot.mp
   rw [← hfaith]
   refine ⟨a.property, ?_⟩
   change inclusion hSB a ∈ B.normalizerMonoidHom.ker at ha
   rw [normalizerMonoidHom_ker] at ha
   exact ha
 intro hd
 exact aut_card_not_dvd h hc
   ((S.pow_dvd_card_of_pow_dvd_card (n := 12) hd).trans (card_dvd_of_injective f hf))
omit [Finite G] in
private theorem eq_top_of_join [IsSimpleGroup G]
    (S : Sylow 2 G) {B : Subgroup G}
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) (hj : B ⊔ (S : Subgroup G) = ⊤) : B = ⊤ := by
 have hn : normalizer (B : Set G) = ⊤ := top_unique (hj ▸ sup_le B.le_normalizer hSB)
 let : B.Normal := normalizer_eq_top_iff.mp hn
 apply (inferInstance : B.Normal).eq_bot_or_eq_top.resolve_left
 intro hb
 have hd := (cardinal_divisors h).1
 rw [hb,card_bot] at hd
 norm_num at hd
omit [Finite G] in
private theorem map_join_eq_top (S : Sylow 2 G) (B : Subgroup G)
    {H : Type*} [Group H] (e : G ≃* H)
    (h : (B ⊔ (S : Subgroup G)).map e.toMonoidHom = ⊤) :
    B ⊔ (S : Subgroup G) = ⊤ := by
 apply map_injective (f := e.toMonoidHom) e.injective
 rw [h,map_top_of_surjective _ e.surjective]
private theorem eq_top_linear [IsSimpleGroup G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) (h : IsModel (B ⧸ pCore 2 B))
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSL G 3 (2 ^ n)) : B = ⊤ := by
 obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
 by_cases hn1 : n = 1
 · have hd := ((cardinal_divisors h).2).trans B.card_subgroup_dvd_card
   rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF,hn1] at hd
   norm_num at hd
 let : Fintype F := Fintype.ofFinite F
 let : CharP F 2 := charP_of_card_eq_prime_pow
   (by simpa only [Nat.card_eq_fintype_card] using hF)
 let := local_perfect hB
 apply eq_top_of_join S hSB h
 apply map_join_eq_top S B e
 apply Matrix.PSL3.LinearThree.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
   F (p := 3) (by decide) (section_threeRank h) (by omega : 1 < n) hF
   (S.mapSurjective e.surjective) _ (map_mono le_sup_right)
   (e.toMonoidHom.comp B.subtype) (e.injective.comp B.subtype_injective)
 rintro _ ⟨b,rfl⟩
 exact mem_map_of_mem _ (mem_sup_left b.property)
private theorem eq_top_symplectic [IsSimpleGroup G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) (h : IsModel (B ⧸ pCore 2 B))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp G 2 (2 ^ n)) : B = ⊤ := by
 obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
 let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
 let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
 let := local_perfect hB
 have hq : 2 < Nat.card F := by
   rw [hF]
   have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
   norm_num at this
   omega
 apply eq_top_of_join S hSB h
 apply map_join_eq_top S B a
 apply Theory.SpecificGroups.SymplecticFour.perfect_odd_rank_two_sylow_overgroup_eq_top
   (p := 3) (by decide) (section_threeRank h) hq
   (S.mapSurjective a.surjective) _ (map_mono le_sup_right)
   (a.toMonoidHom.comp B.subtype) (a.injective.comp B.subtype_injective)
 rintro _ ⟨b,rfl⟩
 exact mem_map_of_mem _ (mem_sup_left b.property)
private theorem eq_top_g2 [IsSimpleGroup G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) (h : IsModel (B ⧸ pCore 2 B))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassificationModels.IsG2At G (2 ^ n)) : B = ⊤ := by
 obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
 let : Fintype F := Fintype.ofFinite F
 let : CharP F 2 := charP_of_card_eq_prime_pow
   (by simpa only [Nat.card_eq_fintype_card] using hF)
 let := local_perfect hB
 have hq : 2 < Nat.card F := by
   rw [hF]
   have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
   norm_num at this
   omega
 apply eq_top_of_join S hSB h
 apply map_join_eq_top S B e
 apply Atlas.G2.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
   (p := 3) (by decide) (section_threeRank h) hq
   (S.mapSurjective e.surjective) _ (map_mono le_sup_right)
   (e.toMonoidHom.comp B.subtype) (e.injective.comp B.subtype_injective)
 rintro _ ⟨b,rfl⟩
 exact mem_map_of_mem _ (mem_sup_left b.property)
omit [Finite G] in
private theorem embedded_core {H : Type*} [Group H] (e : G ≃* H)
    (B : Subgroup G) (hcore : pCore 2 B ≠ ⊥) :
    ∃ R : Subgroup H, R ≠ ⊥ ∧ IsPGroup 2 R ∧ B.map e.toMonoidHom ≤ normalizer (R : Set H) := by
 let R := (pCore 2 B).map B.subtype
 have hR : R ≠ ⊥ := by
   intro h
   exact hcore ((map_eq_bot_iff_of_injective (pCore 2 B) B.subtype_injective).mp h)
 refine ⟨R.map e.toMonoidHom, ?_, (pCore_isPGroup.map B.subtype).map e.toMonoidHom, ?_⟩
 · intro h
   exact hR ((map_eq_bot_iff_of_injective R (f := e.toMonoidHom) e.injective).mp h)
 · exact (map_mono (B.le_normalizer.trans
     (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))).trans
     (le_normalizer_map e.toMonoidHom)
private theorem not_triality_core_ne_bot
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (h : IsModel (B ⧸ pCore 2 B)) (hcore : pCore 2 B ≠ ⊥)
    {n : ℕ} (hn : 1 ≤ n) (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) G) : False := by
 let hn' : 0 < n := by omega
 obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n hn').mp hm
 obtain ⟨R,hR,hp,hBR⟩ := embedded_core e B hcore
 obtain ⟨g,a,hg⟩ := Triality.Standard.TwoLocalCover.normalizer_cover n hn' R hR hp
 let P := Triality.Standard.Parabolics.parabolic (Triality.Standard.binaryParameters n hn') a
 let j := (MulAut.conj g).toMonoidHom.comp (e.toMonoidHom.comp B.subtype)
 have him : ∀ b, j b ∈ P := by
   intro b
   exact hg (mem_map_of_mem _ (hBR (mem_map_of_mem _ b.property)))
 let f : B →* P := j.codRestrict P him
 have hf : Function.Injective f := fun x y h =>
   B.subtype_injective (e.injective ((MulAut.conj g).injective (congrArg Subtype.val h)))
 let := local_perfect hB
 let : Group.IsPerfect f.range := Group.IsPerfect.range f
 have hd : f.range ≤ commutator P := by
   rw [← commutator_eq_self (H := f.range)]
   exact commutator_mono le_top le_top
 let k := f.codRestrict (commutator P) (fun x => hd ⟨x,rfl⟩)
 have hk : Function.Injective k := fun x y h => hf (congrArg Subtype.val h)
 have hb := (Theory.GroupTheory.primeRank_le_of_injective 3 k hk).trans
   (Triality.Standard.InvolutionFixedRank.derived_parabolic_threeRank_le_one
     (Triality.Standard.binaryParameters n hn') rfl a)
 have := section_threeRank h
 omega
omit [Finite G] in
private theorem not_ree_core_ne_bot {B : Subgroup G}
    (h : IsModel (B ⧸ pCore 2 B)) (hcore : pCore 2 B ≠ ⊥)
    {m : ℕ} (hm : 1 ≤ m) (e : G ≃* ReeF4.Model m) : False := by
 obtain ⟨R,hR,hp,hBR⟩ := embedded_core e B hcore
 apply ReeF4.ConverseParabolics.normalizer_fifteen_free hm R hR hp
 have hd := card_dvd_of_le hBR
 rw [card_map_of_injective e.injective] at hd
 exact ((cardinal_divisors h).1).trans hd
private theorem large_power_dvd {a b : ℕ} (h : 12 ≤ a * b) : 4096 ∣ (2 ^ a) ^ b := by
 rw [← pow_mul]
 exact Nat.pow_dvd_pow 2 h
omit [Finite G] in
private theorem triality_large {n : ℕ} (hn : 1 ≤ n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) G) : 4096 ∣ Nat.card G := by
 obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n (by omega)).mp hm
 let P := Triality.Standard.binaryParameters n (by omega : 0 < n)
 have hd := (Triality.Standard.Parabolics.unipotent P).card_subgroup_dvd_card
 rw [Triality.Standard.Parabolics.card_unipotent_binary P rfl] at hd
 change (2 ^ n) ^ 12 ∣ Nat.card (Triality.Standard.BinaryCarrier n _) at hd
 rw [← Nat.card_congr e.toEquiv] at hd
 exact (large_power_dvd (by omega : 12 ≤ n * 12)).trans hd
omit [Finite G] in
private theorem ree_large (m : ℕ) (e : G ≃* ReeF4.Model m) : 4096 ∣ Nat.card G := by
 have hd := (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
 rw [ReeF4.Parabolics.card_unipotent,← Nat.card_congr e.toEquiv] at hd
 exact (large_power_dvd (by omega : 12 ≤ (2 * m + 1) * 12)).trans hd

theorem eq_top_of_rankTwo [IsSimpleGroup G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B))
    {n : ℕ} (hm : ChapterA.Section02.IsTheoremCRankTwoModel G n) : B = ⊤ := by
 cases hm with
 | linear hn hm => exact eq_top_linear S hB hSB h hn hm
 | symplectic hn hm => exact eq_top_symplectic S hB hSB h hn hm
 | g2 hn hm => exact eq_top_g2 S hB hSB h hn hm
 | triality hn hm =>
   by_cases hc : pCore 2 B = ⊥
   · exact (not_large_twoPart S
       ((MainConverse.ExceptionalLocal.triality_even_quasithin_evenCharacteristic hn hm).2 S)
       hB hSB h hc (triality_large hn hm)).elim
   · exact (not_triality_core_ne_bot S hB h hc hn hm).elim
 | ree_f4 m hm _ he =>
   by_cases hc : pCore 2 B = ⊥
   · exact (not_large_twoPart S
       ((MainConverse.ReeLocal.quasithin_evenCharacteristic_of_iso hm he.some).2 S)
       hB hSB h hc (ree_large m he.some)).elim
   · exact (not_ree_core_ne_bot h hc hm he.some).elim
 | symplectic_derived _ he =>
   have hd := ((cardinal_divisors h).2).trans B.card_subgroup_dvd_card
   rw [Nat.card_congr (he.some.trans
     Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
     nat_card_alternatingGroup] at hd
   norm_num at hd
 | g2_derived _ he =>
   have hd := ((cardinal_divisors h).2).trans B.card_subgroup_dvd_card
   rw [Nat.card_congr he.some.toEquiv,
     Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
   norm_num at hd
 | tits _ he =>
   have hd := ((cardinal_divisors h).2).trans B.card_subgroup_dvd_card
   rw [Nat.card_congr he.some.toEquiv,Tits.parrottGroup_card] at hd
   norm_num at hd

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional

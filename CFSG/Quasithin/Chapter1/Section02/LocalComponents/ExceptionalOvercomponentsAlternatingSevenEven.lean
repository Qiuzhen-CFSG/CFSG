module
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.EvenModels
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.Alternating.Aut
/-!
# The even-rank-two rows above an A₇ local section

Three-rank at least two forces the original perfect section and its full
Sylow to generate the PSL₃, Sp₄ and G₂ containing models. In the triality
and Ree rows, a nontrivial two-core contradicts parabolic rank or order;
a trivial core would make the full Sylow act faithfully on A₇, contradicting
Aut(A₇)=S₇. The remaining small rows fail the section's divisor35.
The final application retains the literal local quotients and the simplicity
premise of the source's simple-component case.

Source: Aschbacher–Smith A.3.12(2–3), pp.47–48, and 1.2.8, pp.506–507.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenEven
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem section_card_dvd {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) : 2520 ∣ Nat.card B := by
 have hc : Nat.card (B ⧸ pCore 2 B) = 2520 := by
   rw [Nat.card_congr h.some.toEquiv, nat_card_alternatingGroup]
   norm_num
 exact hc ▸ card_quotient_dvd_card (pCore 2 B)

private theorem section_threeRank {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) : 2 ≤ primeRank 3 B := by
 rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
   primeRank_congr 3 h.some]
 exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)

omit [Finite G] in
private theorem cardinal_divisors {B : Subgroup G} (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) :
    15 ∣ Nat.card B ∧ 35 ∣ Nat.card B :=
  ⟨(by decide : 15 ∣ 2520).trans (section_card_dvd h),
    (by decide : 35 ∣ 2520).trans (section_card_dvd h)⟩
omit [Finite G] in
private theorem aut_card_not_dvd {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (hc : pCore 2 B = ⊥) : ¬ 4096 ∣ Nat.card (MulAut B) := by
 let q : B ≃* B ⧸ pCore 2 B :=
   ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm
 let c : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
   MulEquiv.ofBijective MulAut.conjNormal
     (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
 rw [Nat.card_congr (MulAut.congr (q.trans h.some)).toEquiv,
   ← Nat.card_congr c.toEquiv, Nat.card_perm, Nat.card_fin]
 decide
private theorem not_large_twoPart
    (S : Sylow 2 G) (hE : IsEvenCharacteristicAt S)
    {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) (hc : pCore 2 B = ⊥) :
    ¬ 4096 ∣ Nat.card G := by
 let q : B ⧸ pCore 2 B ≃* B :=
   (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
 let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
 let : IsSimpleGroup (B ⧸ pCore 2 B) := h.some.isSimpleGroup
 let : IsSimpleGroup B := q.symm.isSimpleGroup
 let := Exceptional.local_perfect hB
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
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) (hj : B ⊔ (S : Subgroup G) = ⊤) : B = ⊤ := by
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
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSL G 3 (2 ^ n)) : B = ⊤ := by
 obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
 by_cases hn1 : n = 1
 · have hd := ((cardinal_divisors h).2).trans B.card_subgroup_dvd_card
   rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF,hn1] at hd
   norm_num at hd
 let : Fintype F := Fintype.ofFinite F
 let : CharP F 2 := charP_of_card_eq_prime_pow
   (by simpa only [Nat.card_eq_fintype_card] using hF)
 let := Exceptional.local_perfect hB
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
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp G 2 (2 ^ n)) : B = ⊤ := by
 obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
 let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
 let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
 let := Exceptional.local_perfect hB
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
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassificationModels.IsG2At G (2 ^ n)) : B = ⊤ := by
 obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
 let : Fintype F := Fintype.ofFinite F
 let : CharP F 2 := charP_of_card_eq_prime_pow
   (by simpa only [Nat.card_eq_fintype_card] using hF)
 let := Exceptional.local_perfect hB
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
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) (hcore : pCore 2 B ≠ ⊥)
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
 let := Exceptional.local_perfect hB
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
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) (hcore : pCore 2 B ≠ ⊥)
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
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
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


/-- The genuine simple even-rank-two branch of the local-overcomponent
inspection preserves the literal A₇ quotient. -/
theorem local_overcomponent_of_rankTwo
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)))
    (hsimple : IsSimpleGroup (K ⧸ pCore 2 K))
    {n : ℕ} (hmodel : ChapterA.Section02.IsTheoremCRankTwoModel (K ⧸ pCore 2 K) n) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) := by
  let H := K ⊔ (T : Subgroup G)
  have hXH : X ≤ H := hXK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hx : X.subgroupOf H ∈ L H (S : Subgroup H) :=
    (mem_LIn_iff_subgroupOf le_sup_right hXH).mp ⟨hXH,hX⟩
  have hn' : (S : Subgroup H) ≤ normalizer (X.subgroupOf H : Set H) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : G)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hb : (X.subgroupOf H).map q ∈ localCComponents Sbar :=
    mem_L_map_twoCore_mem_localCComponents hx
  have hnb : (Sbar : Subgroup (H ⧸ pCore 2 H)) ≤
      normalizer ((X.subgroupOf H).map q : Set _) :=
    (map_mono hn').trans (le_normalizer_map q)
  let eX := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hXH))
  have hk : IsPGroup 2 (q.subgroupMap (X.subgroupOf H)).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eB := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap (X.subgroupOf H)) (q.subgroupMap_surjective _) hk
  have hm : Nonempty ((((X.subgroupOf H).map q) ⧸ pCore 2 ((X.subgroupOf H).map q)) ≃*
      alternatingGroup (Fin 7)) := ⟨eB.symm.trans (eX.trans h.some)⟩
  let := pCore_isNilpotent (p := 2) (G := H)
  have hC := hK.1.map_quotient (pCore 2 H)
  have hBC : (X.subgroupOf H).map q ≤ (K.subgroupOf H).map q :=
    map_mono (comap_mono hXK)
  obtain ⟨P,_,hl,hs⟩ := exists_local_sylow_normalizing Sbar hb hC.subnormal hBC hnb
  let er := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBC)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hBC))
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show K ≤ H from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)))
  let eC := (cComponentTwoCoreQuotientEquiv hK.1).symm.trans eK
  let := hsimple
  let : IsSimpleGroup ((K.subgroupOf H).map q) := eC.isSimpleGroup
  have hh : Nonempty (((((X.subgroupOf H).map q).subgroupOf ((K.subgroupOf H).map q)) ⧸
      pCore 2 ((((X.subgroupOf H).map q).subgroupOf ((K.subgroupOf H).map q)))) ≃*
      alternatingGroup (Fin 7)) := ⟨er.trans hm.some⟩
  have ht := eq_top_of_rankTwo P hl hs hh (hmodel.of_mulEquiv eC)
  let eD := (MulEquiv.subgroupCongr ht).trans topEquiv
  have hOC : pCore 2 ((K.subgroupOf H).map q) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hC.subnormal, pCore_quotient_pCore_eq_bot 2]
    exact (((K.subgroupOf H).map q).subtype.ker_eq_bot
      ((K.subgroupOf H).map q).subtype_injective)
  let eqD := (QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)).trans
    ((QuotientGroup.quotientMulEquivOfEq hOC).trans QuotientGroup.quotientBot)
  exact ⟨eC.symm.trans (eqD.symm.trans hh.some)⟩

end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenEven

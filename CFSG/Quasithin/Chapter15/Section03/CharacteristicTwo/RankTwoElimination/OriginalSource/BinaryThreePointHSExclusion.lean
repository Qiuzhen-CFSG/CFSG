module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSporadicPlacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalCoreStructure
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCoreJoin
public import CFSG.Quasithin.MainConverse.SporadicLocal.HS
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.CentralCoverCore
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.RankOneFourNormalizer.Fixed
public import Theory.ElementaryAbelian.Injective

/-!
# The actual Higman–Sims local binary-three subgroup

Full-Sylow local coverage and the factor seven force the literal elementary-eight
normalizer. Its perfectness then makes the source local subgroup the whole
normalizer. Its moving two-core is C4 cubed, whereas an abelian image of the
original core is elementary because Q′=Phi(Q).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.BlockNormalizer
private theorem binary_three_core_ne_bot_of_even
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ localCComponents S) (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hE : IsEvenCharacteristicAt S) (h32 : 32 ∣ Nat.card G) : pCore 2 B ≠ ⊥ := by
  intro hc
  let e : B ≃* PSL(3,ZMod 2) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans eB
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup B := e.isSimpleGroup
  let : Group.IsPerfect B := by
    let := hB.perfect
    let a := subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)
    exact Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S hE hB hSB
  let f := B.normalizerMonoidHom.comp (inclusion hSB)
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hf]
    refine ⟨x.property,?_⟩
    change inclusion hSB x ∈ B.normalizerMonoidHom.ker at hx
    rwa [normalizerMonoidHom_ker] at hx
  have hd := card_dvd_of_injective f hi
  rw [Nat.card_congr (MulAut.congr e).toEquiv,Matrix.PSL3Two.Automorphisms.card_aut] at hd
  exact (by decide : ¬32 ∣ 336) ((S.pow_dvd_card_of_pow_dvd_card (n := 5) h32).trans hd)

private theorem maximal_overgroup_of_core {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {B : Subgroup G}
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) (hc : pCore 2 B ≠ ⊥) :
    ∃ N : Subgroup G, IsMaximalTwoLocal N ∧ normalizer (B : Set G) ≤ N ∧
      (S : Subgroup G) ≤ N := by
  let U := (pCore 2 B).map B.subtype
  have hU : U ≠ ⊥ := fun he => hc ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hl : IsTwoLocal (normalizer (U : Set G)) := ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩
  obtain ⟨N,hUN,hN⟩ := Finite.exists_le_maximal hl
  have hBN : normalizer (B : Set G) ≤ N :=
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B)).trans hUN
  exact ⟨N,hN,hBN,hSB.trans hBN⟩


private theorem local_zero_seven_free : ¬ 7 ∣ Nat.card (localGroup 0) := by
  let f := CentralNormalizerThreePart.PairQuotient.fiveHom
  have hk : IsPGroup 2 f.ker := by
    rw [CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]
    exact CentralInvolutionCore.core_isPGroup
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hc := f.ker.card_mul_index
  rw [index_ker,hn] at hc
  intro hd
  rw [←hc] at hd
  have hr : 7 ∣ Nat.card f.range :=
    ((by decide : Nat.Coprime 7 2).pow_right n).dvd_of_dvd_mul_left hd
  have hh := hr.trans f.range.card_subgroup_dvd_card
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm] at hh

private theorem local_one_seven_free : ¬ 7 ∣ Nat.card (localGroup 1) := by
  let E := elementary 1
  let f := E.normalizerMonoidHom
  have hk : IsPGroup 2 f.ker := by
    rw [normalizerMonoidHom_ker]
    exact (large_elementary_centralizer_isPGroup 1 (by decide)).of_equiv
      (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (E : Set Carrier))).symm
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hc := f.ker.card_mul_index
  rw [index_ker,hn] at hc
  have he : Nat.card E=4 := by
    exact RankOneFourNormalizer.elementary_card 1
  let := elementary_isElementaryAbelian 1
  have ha : Nat.card (MulAut E)=6 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E 2 he]
    norm_num [Fin.prod_univ_succ]
  intro hd
  change 7 ∣ Nat.card (normalizer (E : Set Carrier)) at hd
  rw [←hc] at hd
  have hr : 7 ∣ Nat.card f.range :=
    ((by decide : Nat.Coprime 7 2).pow_right n).dvd_of_dvd_mul_left hd
  have hh := hr.trans f.range.card_subgroup_dvd_card
  rw [ha] at hh
  norm_num at hh

private theorem base_normalized_eq_top
    (S : Sylow 2 baseNormalizer) (A : Subgroup baseNormalizer)
    (hn : (S : Subgroup baseNormalizer) ≤ normalizer A)
    (hd : 168 ∣ Nat.card A) : A=⊤ := by
  have hc : Nat.card baseNormalizer=10752 := CoreGeometry.normalizer_card
  have hs : Nat.card S=512 := by rw [S.card_eq_multiplicity,hc]; decide +kernel
  have hJ : A ⊔ (S : Subgroup baseNormalizer)=⊤ := by
    apply eq_top_of_card_eq
    apply Nat.dvd_antisymm
    · exact card_subgroup_dvd_card _
    · rw [hc]
      have h1 := hd.trans (card_dvd_of_le (show A ≤ A ⊔ (S : Subgroup _) from le_sup_left))
      have h2 : 512 ∣ Nat.card (A ⊔ (S : Subgroup baseNormalizer) : Subgroup baseNormalizer) :=
        hs ▸ card_dvd_of_le (show (S : Subgroup _) ≤ A ⊔ (S : Subgroup _) from le_sup_right)
      simpa only [show Nat.lcm 168 512=10752 from by decide] using Nat.lcm_dvd h1 h2
  let : A.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←hJ]; exact sup_le A.le_normalizer hn))
  have hdq : Nat.card (baseNormalizer ⧸ A) ∣ 2^6 := by
    apply Nat.dvd_of_mul_dvd_mul_left (by decide : 0<168)
    have hh := Nat.mul_dvd_mul_right hd (Nat.card (baseNormalizer ⧸ A))
    rw [←index_eq_card,A.card_mul_index,hc] at hh
    exact hh
  let hp := isPGroup_iff_card_dvd_pow.mpr ⟨6,hdq⟩
  let : Group.IsNilpotent (baseNormalizer ⧸ A) := hp.isNilpotent
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ A)

/-- The actual full-Sylow-normalized local binary-three subgroup in HS
is equivalent to the complete elementary-eight normalizer. -/
theorem binary_three_hs_local_normalizer
    (S : Sylow 2 Carrier) (B : Subgroup Carrier)
    (hB : B ∈ localCComponents S) (hSB : (S : Subgroup Carrier) ≤ normalizer B)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) :
    Nonempty (B ≃* baseNormalizer) := by
  have hc := binary_three_core_ne_bot_of_even S hB hSB eB
    (MainConverse.SporadicLocal.hs_evenCharacteristic S)
    (by rw [NormalizerIndex.card_carrier]; decide)
  obtain ⟨N,hN,hBN,hSN⟩ := maximal_overgroup_of_core S hSB hc
  have hBN' : B ≤ N := B.le_normalizer.trans hBN
  obtain ⟨T,_,_,_,_,hcover⟩ := MainConverse.SporadicLocal.HSEvenLocalCover.exists_normal_local_cover_of_card_dvd
    Sporadic.LeechRelated.HS.card_carrier_dvd
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S T
  let a := MulAut.conj g
  have hTN : (T : Subgroup Carrier) ≤ N.map a.toMonoidHom := by
    have hh := map_mono (f := a.toMonoidHom) hSN
    change ((g • S : Sylow 2 Carrier) : Subgroup Carrier) ≤ _ at hh
    rwa [hg] at hh
  obtain ⟨i,⟨ei⟩⟩ := hcover (N.map a.toMonoidHom)
    (Theory.Quasithin.isMaximalTwoLocal_map a hN) hTN
  have h168 : 168 ∣ Nat.card B := by
    have hq : Nat.card (B ⧸ pCore 2 B)=168 :=
      (Nat.card_congr (eB.trans Matrix.PSL3Two.equiv.symm).toEquiv).trans Matrix.PSL3Two.card_SL
    rw [←hq]
    exact card_quotient_dvd_card _
  have hi : i=2 := by
    have hd : 7 ∣ Nat.card (localGroup i) := by
      rw [←Nat.card_congr ei.toEquiv,card_map_of_injective a.injective]
      exact ((by decide : 7 ∣ 168).trans h168).trans (card_dvd_of_le hBN')
    fin_cases i
    · exact (local_zero_seven_free hd).elim
    · exact (local_one_seven_free hd).elim
    · rfl
  subst i
  let e : N ≃* baseNormalizer := (a.subgroupMap N).trans ei
  let A := B.subgroupOf N
  let P := S.subtype hSN
  have hn : (P : Subgroup N) ≤ normalizer A := by
    rw [Sylow.coe_subtype,←subgroupOf_normalizer_eq hBN']
    exact comap_mono hSB
  let d : B ≃* A.map e.toMonoidHom :=
    (subgroupOfEquivOfLe hBN').symm.trans (e.subgroupMap A)
  have ht := base_normalized_eq_top (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    (A.map e.toMonoidHom) ((map_mono hn).trans (A.le_normalizer_map e.toMonoidHom))
    ((Nat.card_congr d.toEquiv) ▸ h168)
  exact ⟨d.trans ((MulEquiv.subgroupCongr ht).trans topEquiv)⟩

private theorem containing_hs_local_normalizer
    {X : Type*} [Group X] [Finite X] (T : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent)
    (hBK : B ≤ K) (hTB : (T : Subgroup X) ≤ normalizer B)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) (eK : K ≃* Carrier) :
    Nonempty (B ≃* baseNormalizer) := by
  obtain ⟨S,_,hl,hn⟩ := exists_local_sylow_normalizing T hB hK.subnormal hBK hTB
  let A := B.subgroupOf K
  let D := A.map eK.toMonoidHom
  let a : B ≃* D := (subgroupOfEquivOfLe hBK).symm.trans (eK.subgroupMap A)
  let eD := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans eB
  let : Group.IsSolvable eK.toMonoidHom.ker := by
    rw [eK.toMonoidHom.ker_eq_bot eK.injective]
    infer_instance
  have hlD := Chapter1.Section02.localCComponents_map_of_solvable_ker hl eK.toMonoidHom
  have hnD := (map_mono (f := eK.toMonoidHom) hn).trans (A.le_normalizer_map eK.toMonoidHom)
  obtain ⟨d⟩ := binary_three_hs_local_normalizer
    (S.mapSurjective (f := eK.toMonoidHom) eK.surjective) D hlD hnD eD
  exact ⟨a.trans d⟩

private theorem hs_moving_core_equiv
    {X : Type*} [Group X] [Finite X] (B : Subgroup X) (eB : B ≃* baseNormalizer) :
    Nonempty (LinearThree.commutatorCore B ≃* pCore 2 baseNormalizer) := by
  let R := ⁅pCore 2 B,(⊤ : Subgroup B)⁆
  have hR : R.map B.subtype = LinearThree.commutatorCore B := by
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
    rfl
  have he : R.map eB.toMonoidHom = pCore 2 baseNormalizer := by
    rw [map_commutator,pCore_map_iso,map_top_of_surjective eB.toMonoidHom eB.surjective,
      normalizer_core_fully_moved]
  let i : R ≃* LinearThree.commutatorCore B :=
    (R.equivMapOfInjective B.subtype B.subtype_injective).trans (MulEquiv.subgroupCongr hR)
  exact ⟨i.symm.trans ((eB.subgroupMap R).trans (MulEquiv.subgroupCongr he))⟩

private theorem core_not_elementary : ¬ IsElementaryAbelian 2 (pCore 2 baseNormalizer) := by
  intro hE
  let := hE
  let v : Multiplicative (Fin 3 → ZMod 4) := Multiplicative.ofAdd (fun _ => 1)
  let q := CoreGeometry.coreEquiv.symm v
  have hq : q ^ 2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (pCore 2 baseNormalizer)) q
  have hv : v ^ 2=1 := by
    have hh := congrArg CoreGeometry.coreEquiv hq
    simpa only [q,map_pow,map_one,CoreGeometry.coreEquiv.apply_symm_apply] using hh
  have hh := congrArg (fun x : Multiplicative (Fin 3 → ZMod 4) => x.toAdd 0) hv
  norm_num [v,pow_two] at hh
  exact (by decide : (2 : ZMod 4) ≠ 0) hh

private theorem abelian_image_elementary
    {A D : Type*} [Group A] [Finite A] [Group D] [IsMulCommutative D]
    (hp : IsPGroup 2 A) (hPhi : _root_.commutator A=frattini A)
    (f : A →* D) (hf : Function.Surjective f) : IsElementaryAbelian 2 D := by
  let : Fact (IsPGroup 2 A) := ⟨hp⟩
  have hk : frattini A ≤ f.ker := hPhi ▸ Abelianization.commutator_subset_ker f
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  obtain ⟨a,rfl⟩ := hf x
  rw [←map_pow]
  exact hk (pth_power_mem_frattini_of_isPGroup (p := 2) a)

open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The actual original point quotient cannot have an HS containing component:
its abelian moving core would have to be both elementary and C4 cubed. -/
theorem binary_three_source_point_not_hs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    (hK : K.IsCComponent)
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (eK : K ≃* Carrier) : False := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let Q := LinearThree.commutatorCore c.L
  let B := (c.L.subgroupOf C).map q
  let E := (Q.subgroupOf C).map q
  let T := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hQC : Q ≤ C := ((LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)).trans hLC
  obtain ⟨hB,⟨eB⟩⟩ := point_centralizer_quotient_local d c.L e b z hLS P hP
  have hSL : d.S ≤ normalizer c.L := le_sup_right.trans
    ((normal_subgroupOf_iff_le_normalizer (show c.L ≤ c.L ⊔ d.S from le_sup_left)).mp
      b.component_normal)
  have hPB : (P : Subgroup C) ≤ normalizer (c.L.subgroupOf C) := by
    rw [←subgroupOf_normalizer_eq hLC]
    intro x hx
    exact hSL (hP ▸ mem_map_of_mem C.subtype hx)
  have hTB : (T : Subgroup (C ⧸ pCore 2 C)) ≤ normalizer B :=
    (map_mono (f := q) hPB).trans ((c.L.subgroupOf C).le_normalizer_map q)
  obtain ⟨a⟩ := containing_hs_local_normalizer T hB hK hBK hTB eB eK
  obtain ⟨aR⟩ := hs_moving_core_equiv B a
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hE : E=LinearThree.commutatorCore B :=
    binary_three_original_core_image_of_le c.L C hLC q hk
  let eR : E ≃* pCore 2 baseNormalizer := (MulEquiv.subgroupCongr hE).trans aR
  let f : Q →* E := (q.subgroupMap (Q.subgroupOf C)).comp
    (subgroupOfEquivOfLe hQC).symm.toMonoidHom
  have hfq : Function.Surjective f := (q.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hQC).symm.surjective
  let : IsMulCommutative E := .of_comm (fun x y => eR.injective (by rw [map_mul,map_mul,mul_comm]))
  have hp : IsPGroup 2 Q := (c.L.isPGroup_pCoreIn 2).to_le (LinearThree.commutatorCore_le c.L)
  have hPhi : _root_.commutator Q=frattini Q :=
    (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := abelian_image_elementary hp hPhi f hfq
  exact core_not_elementary (IsElementaryAbelian.of_injective eR.symm.toMonoidHom eR.symm.injective)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

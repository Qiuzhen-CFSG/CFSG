module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenOdd
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenJankoFour
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenEven
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenSporadic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ClassicalCoverQuotient
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.OddBender
public import Theory.GroupTheory.PerfectCenterFrattini
/-!
# Complete containing-carrier inspection for an original local A₇ section

The simple Theorem C catalogue leaves only equality, J₂, or M₂₃. The genuine
central three-covers descend through their literal center quotient; all
proper rows are excluded, and a full image would supplement the center in
a perfect group. This contradicts the original centerless A₇ two-core
quotient and its order-three covering center.
Source: Aschbacher–Smith A.3.6, A.3.12 and 1.2.8, pp.43–48,506–507.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenCatalogue
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings AlternatingSevenSection
open Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem section_card {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) :
    Nat.card (B ⧸ pCore 2 B) = 2520 := by
  rw [Nat.card_congr h.some.toEquiv,nat_card_alternatingGroup]
  norm_num

private theorem eq_top_of_card_le (B : Subgroup G)
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (hc : Nat.card G ≤ 2520) : B=⊤ := by
  apply B.eq_top_of_card_eq
  apply le_antisymm (Nat.card_le_card_of_injective B.subtype B.subtype_injective)
  apply hc.trans
  rw [← section_card h]
  exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 B))
    (QuotientGroup.mk'_surjective _)

omit [Finite G] in
private theorem not_small_order {H : Type*} [Group H] {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (e : G ≃* H) (hc : ¬ 2520 ∣ Nat.card H) : False := by
  apply hc
  rw [← Nat.card_congr e.toEquiv]
  exact (section_card h ▸ card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card

/-- The complete simple-containing conclusion for the literal local A₇ section. -/
theorem simple_models [IsSimpleGroup G] (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) (hm : TheoremCModel G) :
    B = ⊤ ∨ Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (G ≃* Sporadic.Mathieu.M23) := by
  cases hm with
  | alternating n hnRange he =>
    have hn' : n≤7 ∨ n=8 := by omega
    rcases hn' with hsmall|rfl
    · exact Or.inl (eq_top_of_card_le B h (by
        rw [Nat.card_congr he.some.toEquiv]
        have hn5 := hnRange.1
        interval_cases n <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]))
    · exact (AlternatingSevenBinary.not_binaryFour S B hn h
        ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,
          ⟨he.some.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩).elim
  | linear_odd p e hp ho he hs hm =>
    exact (AlternatingSevenOdd.not_odd_linear_two B h hp
      (by rcases he with rfl|rfl <;> decide) hm).elim
  | three_odd p hp ho un hm =>
    cases un
    · exact (AlternatingSevenOdd.not_odd_three S B hB hn h hp ho (.inl hm)).elim
    · exact (AlternatingSevenOdd.not_odd_three S B hB hn h hp ho (.inr hm)).elim
  | rank_one hm => exact Or.inl (AlternatingEight.eq_top_of_bender_model S B hB hn hm)
  | rank_two hm =>
    apply Or.inl
    cases hm with
    | linear n hn' hm => exact AlternatingSevenEven.eq_top_of_rankTwo S hB hn h (.linear hn' hm)
    | symplectic n hn' hm => exact AlternatingSevenEven.eq_top_of_rankTwo S hB hn h (.symplectic hn' hm)
    | g2 n hn' hm => exact AlternatingSevenEven.eq_top_of_rankTwo S hB hn h (.g2 hn' hm)
    | triality n hn' hm => exact AlternatingSevenEven.eq_top_of_rankTwo S hB hn h (.triality hn' hm)
    | ree m hm he =>
      exact AlternatingSevenEven.eq_top_of_rankTwo S hB hn h
        (.ree_f4 m hm rfl ((ReeF4.exists_localBlockInput_mulEquiv_iff G m).mp he))
    | symplectic_derived he => exact AlternatingSevenEven.eq_top_of_rankTwo S hB hn h (.symplectic_derived rfl he)
    | g2_derived he => exact AlternatingSevenEven.eq_top_of_rankTwo S hB hn h (.g2_derived rfl he)
    | tits he => exact AlternatingSevenEven.eq_top_of_rankTwo S hB hn h (.tits rfl he)
  | binary_linear n hn' hm => exact (AlternatingSevenBinary.not_binaryFour_or_Five S B hB hn h hn' hm).elim
  | sporadic name hne he =>
    obtain ⟨e⟩ := he
    cases name with
    | m11 => exact (not_small_order h e (by change ¬ 2520 ∣ Nat.card Sporadic.Mathieu.M11; rw [Sporadic.Mathieu.m11_order]; decide)).elim
    | m12 => exact (not_small_order h e (by change ¬ 2520 ∣ Nat.card Sporadic.Mathieu.M12; rw [Sporadic.Mathieu.m12_order]; decide)).elim
    | m22 => exact (AlternatingSevenMathieu.not_mathieuTwentyTwo S B hB hn h e).elim
    | m23 => exact Or.inr (Or.inr ⟨e⟩)
    | m24 => exact (AlternatingSevenMathieu.not_mathieuTwentyFour S B hB hn h e).elim
    | j2 => exact Or.inr (Or.inl ⟨e⟩)
    | j3 => exact (hne rfl).elim
    | j4 => exact (AlternatingSevenJankoFour.not_jankoFour S B hB hn h e).elim
    | hs => exact (AlternatingSevenModels.not_higmanSims S B hB hn h e).elim
    | he => exact (AlternatingSevenModels.not_held S B hB hn h e).elim
    | ru => exact (AlternatingSevenModels.not_rudvalis S B hB hn h e).elim
  | janko_one he => exact (not_small_order h he.some (by rw [Janko1.card_model]; decide)).elim

private theorem not_model_of_center_three [Group.IsPerfect G]
    (hc : Nonempty (center G ≃* Multiplicative (ZMod 3)))
    (h : Nonempty ((G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 7))) : False := by
 let π := QuotientGroup.mk' (pCore 2 G)
 let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
 let : IsSimpleGroup (G ⧸ pCore 2 G) := h.some.isSimpleGroup
 let : Group.IsPerfect (G ⧸ pCore 2 G) := Group.IsPerfect.ofSurjective (f := π)
   (QuotientGroup.mk'_surjective _)
 have hz : center (G ⧸ pCore 2 G) = ⊥ :=
   (inferInstance : (center (G ⧸ pCore 2 G)).Normal).eq_bot_or_eq_top.resolve_right
     (fun ht => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht))
 have hZ : center G ≤ pCore 2 G := by
   intro x hx
   apply (QuotientGroup.eq_one_iff _).mp
   apply mem_bot.mp
   rw [← hz]
   apply mem_center_iff.mpr
   intro y
   obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) y
   exact (map_mul π y x).symm.trans
     ((congrArg π (mem_center_iff.mp hx y)).trans (map_mul π x y))
 have hp : IsPGroup 2 (center G) := pCore_isPGroup.of_injective
   (inclusion hZ) (inclusion_injective hZ)
 obtain ⟨n,hn⟩ := hp.exists_card_eq
 have hcard : Nat.card (center G) = 3 := by
   rw [Nat.card_congr hc.some.toEquiv]
   simp
 rw [hcard] at hn
 have hcop := (by decide : Nat.Coprime 3 2).pow_right n
 rw [← hn] at hcop
 norm_num at hcop

private theorem not_section_of_center_three_of_full_image [Group.IsPerfect G]
    (hc : Nonempty (center G ≃* Multiplicative (ZMod 3)))
    {B : Subgroup G} (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (ht : B.map (QuotientGroup.mk' (center G)) = ⊤) : False := by
 have hsup : B ⊔ center G = ⊤ := by
   have he := congrArg (Subgroup.comap (QuotientGroup.mk' (center G))) ht
   simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using he
 have hb : B = ⊤ := eq_top_of_sup_center_eq_top B hsup
 let e : G ≃* B := ((MulEquiv.subgroupCongr hb).trans topEquiv).symm
 have hh : Nonempty ((G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 7)) :=
   ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans h.some⟩
 exact not_model_of_center_three hc hh

/-- The original order-three center excludes all three-cover rows for the
actual local A₇ two-core section. -/
theorem not_threeCover [IsQuasisimple G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (hc : Nonempty (center G ≃* Multiplicative (ZMod 3)))
    (hm : ThreeCoverModel G) : False := by
 let π := QuotientGroup.mk' (center G)
 let : Group.IsSolvable π.ker := by
   change Group.IsSolvable (QuotientGroup.mk' (center G)).ker
   rw [QuotientGroup.ker_mk']
   exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
 let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
 let T := S.mapSurjective (QuotientGroup.mk'_surjective (center G))
 obtain ⟨hl,hn,ha⟩ := local_section_map hB hSB h π
 have hl' : B.map π ∈ localCComponents T := hl
 have hn' : (T : Subgroup (G ⧸ center G)) ≤ normalizer (B.map π : Set _) := hn
 cases hm with
 | classical unitary q hq hm =>
   rcases ClassicalCoverQuotient.models unitary q hq hm with ho | he | ⟨n,hpos,hr⟩
   · exact AlternatingSevenOdd.not_odd_model T (B.map π) hl' hn' ha ho
   · exact not_section_of_center_three_of_full_image hc h
       (AlternatingEight.eq_top_of_bender_model T (B.map π) hl' hn' he)
   · have ht := AlternatingSevenEven.eq_top_of_rankTwo T hl' hn' ha (.linear hpos hr)
     exact not_section_of_center_three_of_full_image hc h ht
 | alternating_six hm =>
   obtain ⟨_,_,⟨e⟩⟩ := hm
   have hd := (section_card ha ▸ card_quotient_dvd_card (pCore 2 (B.map π))).trans
     (B.map π).card_subgroup_dvd_card
   rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hd
   norm_num at hd
 | alternating_seven hm =>
   obtain ⟨_,_,⟨e⟩⟩ := hm
   have ht : B.map π=⊤ := eq_top_of_card_le _ ha (by
     rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
     norm_num)
   exact not_section_of_center_three_of_full_image hc h ht
 | mathieu hm =>
   exact AlternatingSevenMathieu.not_mathieuTwentyTwo T (B.map π) hl' hn' ha hm.2.2.some
omit [Finite G] in
private theorem model_of_top_section [IsSimpleGroup G] (B : Subgroup G)
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) (ht : B = ⊤) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) := by
  let eB : B ≃* G := (MulEquiv.subgroupCongr ht).trans topEquiv
  let : IsSimpleGroup B := eB.isSimpleGroup
  have hc : pCore 2 B = ⊥ := by
    rcases (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · have hh := section_card h
      simp [hc] at hh
  let q : B ≃* B ⧸ pCore 2 B := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact ⟨eB.symm.trans (q.trans h.some)⟩

/-- Complete A₇ containing-component inspection over the full known-simple
catalogue, including the genuine three-cover alternatives. -/
theorem containing_models_of_core_eq_bot
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) :
    Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (K ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (K ≃* Sporadic.Mathieu.M23) := by
  let : IsQuasisimple K := alternatingSeven_containing_quasisimple hG hO T hB hK hBK h
  obtain ⟨S,_,hl,hn⟩ := exists_local_sylow_normalizing T hB hK.subnormal hBK hTB
  let e := subgroupOfEquivOfLe hBK
  have hsmall : Nonempty (((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) ≃*
      alternatingGroup (Fin 7)) :=
    ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans h.some⟩
  rcases quasisimple_containing_component_models_knownSimple hG hO hK with
    ⟨hs,hm⟩|⟨hc,hm⟩
  · let : IsSimpleGroup K := hs
    rcases simple_models S (B.subgroupOf K) hl hn hsmall hm with he|hm
    · exact Or.inl (model_of_top_section _ hsmall he)
    · exact Or.inr hm
  · exact (not_threeCover S hl hn hsmall hc hm).elim

/-- The complete local-overcomponent result retains the original X and K,
full Sylow normalization and their literal quotients by the intrinsic cores. -/
theorem alternatingSeven_local_overcomponent
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ Chapter1.L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) := by
  let H := K ⊔ (T : Subgroup G)
  have hXH : X ≤ H := hXK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hx : X.subgroupOf H ∈ Chapter1.L H (S : Subgroup H) :=
    (mem_LIn_iff_subgroupOf le_sup_right hXH).mp ⟨hXH,hX⟩
  have hn' : (S : Subgroup H) ≤ normalizer (X.subgroupOf H : Set H) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : G)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hbar : (X.subgroupOf H).map q ∈ localCComponents Sbar :=
    mem_L_map_twoCore_mem_localCComponents hx
  have hnorm : (Sbar : Subgroup (H ⧸ pCore 2 H)) ≤
      normalizer ((X.subgroupOf H).map q : Set _) :=
    (map_mono hn').trans (le_normalizer_map q)
  have hq := uniqueness_local_quotient_sqtk hG hK.2.2
  let eX := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hXH))
  have hkX : IsPGroup 2 (q.subgroupMap (X.subgroupOf H)).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eB := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap (X.subgroupOf H)) (q.subgroupMap_surjective _) hkX
  have hm : Nonempty ((((X.subgroupOf H).map q) ⧸ pCore 2 ((X.subgroupOf H).map q)) ≃*
      alternatingGroup (Fin 7)) := ⟨eB.symm.trans (eX.trans h.some)⟩
  let := pCore_isNilpotent (p := 2) (G := H)
  have he := containing_models_of_core_eq_bot
    hq (pCore_quotient_pCore_eq_bot 2) Sbar hbar (hK.1.map_quotient _)
    (map_mono (comap_mono hXK)) hnorm hm
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show K ≤ H from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)))
  let f := (cComponentTwoCoreQuotientEquiv hK.1).symm.trans eK
  rcases he with ha|hj|hm
  · exact Or.inl ⟨f.symm.trans ha.some⟩
  · exact Or.inr (Or.inl ⟨f.symm.trans hj.some⟩)
  · exact Or.inr (Or.inr ⟨f.symm.trans hm.some⟩)

end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenCatalogue

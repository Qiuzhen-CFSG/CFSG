module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.Models
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.PermutingSupCard
public import Theory.Mathieu.M22.Properties.QuinticSylowOvergroups
public import Theory.Mathieu.M23.Properties.QuinticSylowOvergroups
public import Theory.Mathieu.M24.Properties.QuinticSylowOvergroups

/-!
# The original quintic actor excludes the three large Mathieu quotients

The nonzero original plane puts its centralizer in the source rank bound.
The actual model's cubic rank and outer-two facts identify L as its cubic
residual, hence normalize L by the whole original Sylow centralizer S.
The genuine quintic actor Y permutes with S and acts nontrivially on L.
Faithful descent through the perfect central cover supplies a subgroup of
its actual quotient containing a full Sylow two-subgroup, with five dividing
its order and no other odd prime. Native M₂₂, M₂₃ and M₂₄ geometry excludes
this subgroup. No generation or global residual premise is used.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]

private theorem raw_cubic_component_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {V Z1 L : Subgroup G} [IsElementaryAbelian 2 V]
    (hZ : Z1 ≤ V) (hZne : Z1 ≠ ⊥)
    (hLc : L ∈ Chapter1.cComponentsIn (centralizer (Z1 : Set G)))
    [IsQuasisimple (L ⧸ pCore 2 L)] (hf : Facts (L ⧸ pCore 2 L)) :
    centralizer (Z1 : Set G) ≤ normalizer (L : Set G) := by
  let G1 := centralizer (Z1 : Set G)
  have hrG : primeRank 3 G1 ≤ 2 :=
    (caseI_centralizer_sqtk hG Z1 hZne
      ((IsElementaryAbelian.isPGroup 2 V).to_le hZ)).stronglyQuasithin
        3 Nat.prime_three (by decide)
  let K := L.subgroupOf G1
  let a : K ≃* L := subgroupOfEquivOfLe hLc.1
  let b : (K ⧸ pCore 2 K) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv b.symm
  have hF := Facts.of_equiv b hf
  have he := hLc.2.eq_primeToResidual_three_of_rank_outer_two
    hF.1 hF.2.1 hrG hF.2.2
  have hLres : L = (primeToResidual 3 G1).map G1.subtype := by
    have hh := congrArg (map G1.subtype) he
    rwa [map_subgroupOf_eq_of_le hLc.1] at hh
  rw [hLres]
  have hh := (primeToResidual 3 G1).le_normalizer_map G1.subtype
  rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh

private theorem raw_two_five_sylow_overgroup
    (T : Sylow 2 G) {Z1 L Y : Subgroup G} [Group.IsPerfect L]
    (hcenter : center L = pCore 2 L)
    (hSyl : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hLN : centralizer (Z1 : Set G) ≤ normalizer (L : Set G))
    (hY : IsPGroup 5 Y) (hYN : Y ≤ normalizer (L : Set G))
    (hYn : ¬ Y ≤ centralizer (L : Set G))
    (hperm : ((((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) : Subgroup G) : Set G) *
      (Y : Set G) = (Y : Set G) *
        ((((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) : Subgroup G) : Set G))
    {X : Type*} [Group X] (e : (L ⧸ pCore 2 L) ≃* X) (hf : Facts X) :
    ∃ (P : Sylow 2 X) (H : Subgroup X) (a b : ℕ),
      (P : Subgroup X) ≤ H ∧ 5 ∣ Nat.card H ∧ Nat.card H ∣ 2^a * 5^b := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let : Finite X := Finite.of_equiv (L ⧸ pCore 2 L) e.toEquiv
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',
      ←hcenter]
  let c : PerfectCentralCovering.Cover L X := ⟨q,hq,inferInstance,hker.le⟩
  let N := normalizer (L : Set G)
  let f := (c.autMap hker).comp L.normalizerMonoidHom
  let U := S ⊔ Y
  have hUN : U ≤ N := sup_le (inf_le_right.trans hLN) hYN
  let A := (U.subgroupOf N).map f
  let B := (Y.subgroupOf N).map f
  have hB : IsPGroup 5 B :=
    (hY.of_equiv (subgroupOfEquivOfLe hYN).symm).map f
  have hBne : B ≠ ⊥ := by
    intro he
    apply hYn
    intro y hy l hl
    have hh : f ⟨y,hYN hy⟩ = 1 := mem_bot.mp (he ▸ mem_map_of_mem f hy)
    have hh' : L.normalizerMonoidHom ⟨y,hYN hy⟩ = 1 :=
      (c.autMap_injective hker) (hh.trans (map_one (c.autMap hker)).symm)
    have ha := congrArg Subtype.val (DFunLike.congr_fun hh' (⟨l,hl⟩ : L))
    change y*l*y⁻¹=l at ha
    exact (mul_inv_eq_iff_eq_mul.mp ha).symm
  have hBI : B ≤ MulAut.innerSubgroup X := by
    let r := QuotientGroup.mk' (MulAut.innerSubgroup X)
    intro b hb
    apply (QuotientGroup.eq_one_iff _).mp
    obtain ⟨i,hi⟩ := hB ⟨b,hb⟩
    obtain ⟨j,hj⟩ := hf.2.2 (r b)
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 5 2).pow i j)
    · apply orderOf_dvd_of_pow_eq_one
      change (r b)^(5^i)=1
      rw [←map_pow,show b^(5^i)=1 from congrArg Subtype.val hi,map_one]
    · exact orderOf_dvd_of_pow_eq_one hj
  let k : X →* MulAut X := MulAut.conj
  have hki : Function.Injective k := conj_injective_of_center_eq_bot hf.1
  let H := A.comap k
  have hHA : H.map k ≤ A := map_comap_le k A
  have hBH : B ≤ H.map k := by
    rw [map_comap_eq]
    exact le_inf hBI (map_mono (comap_mono le_sup_right))
  have hfive : 5 ∣ Nat.card H := by
    have hh := (hB.card_eq_or_dvd.resolve_left (fun he => hBne (card_eq_one.mp he))).trans
      (card_dvd_of_le hBH)
    rwa [card_map_of_injective hki] at hh
  obtain ⟨P,hP⟩ := hSyl
  let Q := P.mapSurjective (f := q) hq
  have hQH : (Q : Subgroup X) ≤ H := by
    rintro x ⟨l,hl,rfl⟩
    let ln : N := ⟨l,L.le_normalizer l.property⟩
    have hlS : (l : G) ∈ S := by
      have hh := hP ▸ mem_map_of_mem L.subtype hl
      exact hh.1
    have hfx : f ln = MulAut.conj (q l) := by
      ext z
      obtain ⟨w,rfl⟩ := hq z
      change c.autMap hker (L.normalizerMonoidHom ln) (q w) = _
      rw [c.autMap_apply hker]
      change q (l*w*l⁻¹)=_
      simp only [map_mul,map_inv,MulAut.conj_apply]
    change k (q l) ∈ A
    rw [←hfx]
    exact mem_map_of_mem f (show ln ∈ U.subgroupOf N from mem_sup_left hlS)
  have hS : IsPGroup 2 S := T.isPGroup'.to_le inf_le_left
  obtain ⟨a,ha⟩ := hS.exists_card_eq
  obtain ⟨b,hb⟩ := hY.exists_card_eq
  have hd : Disjoint S Y := disjoint_of_coprime_natCard (by
    rw [ha,hb]
    exact (by decide : Nat.Coprime 2 5).pow a b)
  have hUcard : Nat.card U = 2^a * 5^b := by
    rw [show U = S ⊔ Y from rfl,card_sup_eq_mul_of_permutes_of_disjoint _ _ hperm hd,ha,hb]
  have hHAcard : Nat.card H ∣ Nat.card A := by
    have hh := card_dvd_of_le hHA
    rwa [card_map_of_injective hki] at hh
  have hAUcard : Nat.card A ∣ Nat.card U := by
    have hh := (U.subgroupOf N).card_map_dvd f
    rwa [Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv] at hh
  exact ⟨Q,H,a,b,hQH,hfive,hUcard ▸ hHAcard.trans hAUcard⟩

/-- The original quintic actor supplies a genuine full-Sylow two-five
overgroup in the same ordinary central quotient. -/
theorem PreparedChosenModule.decomposable_five_raw_two_five_sylow_overgroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let S := (T : Subgroup G) ⊓ G1
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L → IsQuasisimple (L ⧸ pCore 2 L) → Chapter1.IsSylowIn 2 (S ⊓ L) L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ∀ {X : Type*} [Group X], (L ⧸ pCore 2 L) ≃* X → Facts X →
          ∃ (P : Sylow 2 X) (H : Subgroup X) (a b : ℕ),
            (P : Subgroup X) ≤ H ∧ 5 ∣ Nat.card H ∧ Nat.card H ∣ 2^a * 5^b := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R S L hLG hLc hcenter hquasi hSyl hnL hmove X _ e hf
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  obtain ⟨Y,hY,hperfect,hYA,hperm,_,_,_,hBY,_⟩ :=
    s.exists_permuting_quintic_actor hM.1.2 h.normalized h.le_selected c d π hp hs hJi hfive
  have hYC : Y ≤ C := hYA.trans (map_subtype_le _)
  have hYR : Y ≤ R := by
    have hh := embedded_pResidual_mono 2 hYC
    rw [(pResidual_eq_top_iff 2 Y).mpr hperfect,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hWB := (s.full_residual_geometry hM.1.2 h.normalized c d π hp hs hJi).2.1
  have hWY : ⁅⁅localModule T M,R⁆,Y⁆ = ⁅localModule T M,R⁆ := by
    rw [hWB]
    exact hBY
  let : IsQuasisimple (L.subgroupOf G1) := hLc.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
  let : IsQuasisimple (L ⧸ pCore 2 L) := hquasi
  let : Finite X := Finite.of_equiv (L ⧸ pCore 2 L) e.toEquiv
  have hZne : Z1 ≠ ⊥ := (one_lt_card_iff_ne_bot Z1).mp (by
    rw [show Nat.card Z1 = 4 from s.thompson_card s.first]
    decide)
  have hLN : G1 ≤ normalizer (L : Set G) := raw_cubic_component_normalizes hG
    (inf_le_left.trans (plane_le _)) hZne ⟨hLG,hLc.isCComponent⟩ (Facts.of_equiv e hf)
  have hYN : Y ≤ normalizer (L : Set G) := hYR.trans (le_sup_left.trans hnL)
  have hYn : ¬ Y ≤ centralizer (L : Set G) := by
    intro hc
    have hWc : ⁅localModule T M,R⁆ ≤ centralizer (L : Set G) := by
      rw [←hWY,commutator_comm]
      apply commutator_le.mpr
      intro y hy w hw
      exact commutator_mem_centralizer_of_normalizes L (hc hy)
        ((le_sup_right.trans hnL) hw)
    exact hmove (by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hWc)
  exact raw_two_five_sylow_overgroup T hcenter hSyl hLN hY hYN hYn hperm e hf

/-- The same original raw ordinary component has none of the three large
Mathieu two-core quotients; the central two-cover is retained throughout. -/
theorem PreparedChosenModule.decomposable_five_raw_not_large_mathieu
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let S := (T : Subgroup G) ⊓ G1
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L → IsQuasisimple (L ⧸ pCore 2 L) → Chapter1.IsSylowIn 2 (S ⊓ L) L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22) ∧
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M23) ∧
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M24) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R S L hLG hLc hcenter hquasi hSyl hnL hmove
  have hh {X : Type} [Group X] (e : (L ⧸ pCore 2 L) ≃* X) (hf : Facts X) :=
    h.decomposable_five_raw_two_five_sylow_overgroup
      hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
      hLG hLc hcenter hquasi hSyl hnL hmove e hf
  refine ⟨?_,?_,?_⟩
  · rintro ⟨e⟩
    have hf : Facts Sporadic.Mathieu.M22 := CaseIComponentData.facts_of_small_model
      (.inr (.inr (.inl ⟨MulEquiv.refl _⟩)))
    obtain ⟨P,H,a,b,hPH,h5,hc⟩ := hh e hf
    have h3 : ¬3 ∣ Nat.card H := Nat.prime_three.coprime_iff_not_dvd.mp
      ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right
        ((by decide : Nat.Coprime 3 5).pow_right b)).of_dvd_right hc)
    have h11 : ¬11 ∣ Nat.card H := (by decide : Nat.Prime 11).coprime_iff_not_dvd.mp
      ((((by decide : Nat.Coprime 11 2).pow_right a).mul_right
        ((by decide : Nat.Coprime 11 5).pow_right b)).of_dvd_right hc)
    rw [Sporadic.Mathieu.M22QuinticSylow.card_eq_128 P H hPH h3 h11] at h5
    norm_num at h5
  · rintro ⟨e⟩
    have hf : Facts Sporadic.Mathieu.M23 := CaseIComponentData.facts_of_small_model
      (.inr (.inr (.inr (.inl ⟨MulEquiv.refl _⟩))))
    obtain ⟨P,H,a,b,hPH,h5,hc⟩ := hh e hf
    exact Sporadic.Mathieu.M23QuinticSylow.not_five_of_two_five_sylow_overgroup
      P H hPH a b hc h5
  · rintro ⟨e⟩
    have hf : Facts Sporadic.Mathieu.M24 := CaseIComponentData.facts_of_small_model
      (.inr (.inr (.inr (.inr (.inl ⟨MulEquiv.refl _⟩)))))
    obtain ⟨P,H,a,b,hPH,h5,hc⟩ := hh e hf
    have h3 : ¬3 ∣ Nat.card H := Nat.prime_three.coprime_iff_not_dvd.mp
      ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right
        ((by decide : Nat.Coprime 3 5).pow_right b)).of_dvd_right hc)
    rw [Sporadic.Mathieu.M24QuinticSylow.card_eq_1024 P H hPH h3] at h5
    norm_num at h5

end CFSG.Quasithin.Chapter15.Section01

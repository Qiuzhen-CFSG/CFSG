module
public import Stellmacher.SectionTwo.GlobalOffenderFixingFactor
public import Stellmacher.SectionOne.SL2FactorJoinPrime
public import Theory.GroupAction.MinimalNormal

/-!
# Lifting a specified fixing factor to a local subgroup

Under the Section Two hypotheses, a nonidentity vector fixed by the
nontrivial global offender subgroup and by a specified raw one-seven factor
admits a local subgroup above its Sylow centralizer. The subgroup centralizes
the vector and its quotient image contains that same factor.

The global product theorem identifies the offender subgroup with the
intersection of the quotient Sylow and the full factor product. This makes
the vector centralizer a Sylow subgroup of the normal-product overgroup.
Choose a minimal lift of the specified factor inside the vector centralizer.
The SL2 factor join-prime theorem forces a unique maximal Sylow overgroup.
The normal elementary module supplies a nontrivial two-core; equality of the
Sylow with that core would force SL2(2) to normalize its order-two subgroup.

This is the native lifting step for the first factor in Stellmacher (6.4),
Journal of Algebra 190 (1997), p.32. The quotient action and specified factor
are retained; no invariance of that factor under the Sylow is assumed.
Source: refs/latex/stellmacher-n-group.tex and the journal scan.
-/

namespace Stellmacher.SectionTwo
open scoped IsMulCommutative
universe u

private theorem minimal_lift_unique_maximal
    {G X : Type u} [Group G] [Finite G] [Group X]
    (T L : Subgroup G) (q : G →* X) (D : Subgroup X)
    (hTL : T ≤ L) (hDL : D ≤ L.map q) (hDT : ¬ D ≤ T.map q)
    (hprime : ∀ A B : Subgroup G, T ≤ A → T ≤ B → A ≤ L → B ≤ L →
      D ≤ (A ⊔ B).map q → D ≤ A.map q ∨ D ≤ B.map q) :
    ∃ F : Subgroup G, T ≤ F ∧ F ≤ L ∧ D ≤ F.map q ∧ IsUniqueMaximalContaining T F := by
  obtain ⟨F, hF, hFL, hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun A : Subgroup G => T ≤ A ∧ D ≤ A.map q) L ⟨hTL, hDL⟩
  have hTproper : T.subgroupOf F ≠ ⊤ := by
    intro ht
    have hm := congrArg (Subgroup.map F.subtype) ht
    rw [Subgroup.map_subgroupOf_eq_of_le hF.1, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hm
    exact hDT (hm ▸ hF.2)
  obtain ⟨M, hM, hTM⟩ := (eq_top_or_exists_le_coatom (T.subgroupOf F)).resolve_left hTproper
  have hTMamb : T ≤ M.map F.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hF.1]
    exact Subgroup.map_mono hTM
  refine ⟨F, hF.1, hFL, hF.2, M, hM, hTMamb, ?_⟩
  intro N hN hTN
  by_contra hne
  have hjoin : M ⊔ N = ⊤ := by
    apply hM.2
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    have hNM : N ≤ M := heq ▸ le_sup_right
    exact hne ((hN.le_iff_eq hM.1).mp hNM).symm
  have hmapped : M.map F.subtype ⊔ N.map F.subtype = F := by
    rw [← Subgroup.map_sup, hjoin, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hsel := hprime (M.map F.subtype) (N.map F.subtype) hTMamb hTN
    ((Subgroup.map_subtype_le _).trans hFL) ((Subgroup.map_subtype_le _).trans hFL)
    (by rw [hmapped]; exact hF.2)
  have hnot (A : Subgroup F) (hA : A ≠ ⊤) (hTA : T ≤ A.map F.subtype)
      (hDA : D ≤ (A.map F.subtype).map q) : False := by
    have heq := hmin (A.map F.subtype) ⟨hTA, hDA⟩ (Subgroup.map_subtype_le _)
    apply hA
    apply Subgroup.map_injective F.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact heq
  exact hsel.elim (hnot M hM.1 hTMamb) (hnot N hN.1 hTN)

private theorem sylow_of_normal_sup
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (E T : Subgroup G) [E.Normal] (hTS : T ≤ (S : Subgroup G))
    (hSET : (S : Subgroup G) ⊓ E ≤ T) :
    ∃ P : Sylow 2 (↥(E ⊔ T)), (P : Subgroup (↥(E ⊔ T))).map (E ⊔ T).subtype = T := by
  have hTE : T ⊓ E = (S : Subgroup G) ⊓ E :=
    le_antisymm (inf_le_inf_right _ hTS) (le_inf hSET inf_le_right)
  obtain ⟨SE, hSE⟩ := S.exists_subgroupOf_eq_of_normal E
  have hodd : ¬ 2 ∣ (T ⊓ E).relIndex E := by
    rw [hTE, Subgroup.inf_relIndex_right]
    change ¬ 2 ∣ ((S : Subgroup G).subgroupOf E).index
    rw [← hSE]
    exact SE.not_dvd_index
  have hidx : T.relIndex (E ⊔ T) = (T ⊓ E).relIndex E := by
    have h1 := Subgroup.relIndex_mul_relIndex (T ⊓ E) T (E ⊔ T) inf_le_left le_sup_right
    have h2 := Subgroup.relIndex_mul_relIndex (T ⊓ E) E (E ⊔ T) inf_le_right le_sup_left
    have hnorm : E.relIndex (E ⊔ T) = (T ⊓ E).relIndex T := by
      rw [Subgroup.relIndex_sup_left, Subgroup.inf_relIndex_left]
    rw [hnorm] at h2
    have hpos : 0 < (T ⊓ E).relIndex T := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    nlinarith
  let TP := T.subgroupOf (E ⊔ T)
  have hTp : IsPGroup 2 TP := (S.isPGroup'.to_le hTS).comap_of_injective
    (E ⊔ T).subtype (E ⊔ T).subtype_injective
  have hTidx : ¬ 2 ∣ TP.index := by
    change ¬ 2 ∣ T.relIndex (E ⊔ T)
    rwa [hidx]
  refine ⟨hTp.toSylow hTidx, ?_⟩
  rw [IsPGroup.toSylow_coe]
  exact Subgroup.map_subgroupOf_eq_of_le le_sup_right

/-- Lift the specified factor fixing a nonzero offender-fixed vector. -/
public theorem fixing_factor_local_lift
    {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
    (h : Hypotheses G) (S : Sylow 2 G)
    (q : G →* X) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S) :
    letI := quotientConjugationAction S q hq hker
    let J := SectionOne.oneJ (V := vSubgroup S) ((S : Subgroup G).map q)
    let E := (SectionOne.oneE (V := vSubgroup S) ((S : Subgroup G).map q)).comap q
    J ≠ ⊥ → ∀ w : vSubgroup S, w ≠ 1 → w ∈ FixedPoints.subgroup J (vSubgroup S) →
      ∀ D : Subgroup X, SectionOne.IsOneSevenFactor (V := vSubgroup S) D →
        w ∈ FixedPoints.subgroup D (vSubgroup S) →
        let T := (S : Subgroup G) ⊓ Subgroup.centralizer ({(w : G)} : Set G)
        ∃ F : Subgroup G, F ∈ SectionThree.PSet (E ⊔ T) T ∧
          D ≤ F.map q ∧ F ≤ Subgroup.centralizer ({(w : G)} : Set G) := by
  classical
  let V := vSubgroup S
  let _ := quotientConjugationAction S q hq hker
  let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let Sbar := S.mapSurjective hq
  let J := SectionOne.oneJ (V := V) (Sbar : Subgroup X)
  let Ebar := SectionOne.oneE (V := V) (Sbar : Subgroup X)
  let E := Ebar.comap q
  change J ≠ ⊥ → _
  intro hJ w hwne hwJ D hD hwD
  let T := (S : Subgroup G) ⊓ Subgroup.centralizer ({(w : G)} : Set G)
  let L := (E ⊔ T) ⊓ Subgroup.centralizer ({(w : G)} : Set G)
  have hTbarne : (Sbar : Subgroup X) ≠ ⊥ := by
    intro hb
    exact hJ (bot_unique (hb ▸ (show J ≤ (Sbar : Subgroup X) from sSup_le fun _ hA => hA.1)))
  have hdvd : 2 ∣ Nat.card Sbar := Sbar.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hTbarne (Subgroup.card_eq_one.mp hc))
  let _ : Group.IsSolvable G := h.solvable
  have hOne : SectionOne.Hypotheses X V :=
    ⟨Group.isSolvable_of_surjective hq,
      even_iff_two_dvd.mpr (hdvd.trans (Sbar : Subgroup X).card_subgroup_dvd_card),
      quotientConjugationAction_faithful S q hq hker, lemma_two_one h S q hq hker⟩
  obtain ⟨hEn, hprod, _⟩ := SectionOne.oneSeven_global_product hOne Sbar
  obtain ⟨hJid, hEid⟩ := SectionOne.oneSeven_global_identification hOne Sbar
  change Ebar = SectionOne.oneSevenGenerated (G := X) (V := V) at hEid
  let _ : Ebar.Normal := hEid ▸ hEn
  let _ : E.Normal := inferInstance
  have hDE : D ≤ Ebar := by rw [hEid]; exact le_sSup hD
  have hED : Ebar ≤ Subgroup.normalizer (D : Set X) := by
    rw [hEid]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sSup hD)).mp
      (hprod.2.1 D ((SectionOne.mem_oneSevenFactors_iff D).mpr hD))
  have hQcard : Nat.card (↥((Sbar : Subgroup X) ⊓ D)) = 2 :=
    (SectionOne.sl2_product_sylow_coordinates Sbar _ hEn _ hprod
      (fun F hF => ((SectionOne.mem_oneSevenFactors_iff F).mp hF).1)).2.2.2
        D ((SectionOne.mem_oneSevenFactors_iff D).mpr hD)
  have hfix_iff (g : G) : q g • w = w ↔ g ∈ Subgroup.centralizer ({(w : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hh
      have he := congrArg Subtype.val hh
      rw [quotientConjugationAction_smul_coe S q hq hker] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hh
      apply Subtype.ext
      rw [quotientConjugationAction_smul_coe S q hq hker, hh, mul_inv_cancel_right]
  have hSET : (S : Subgroup G) ⊓ E ≤ T := by
    intro s hs
    refine ⟨hs.1, (hfix_iff s).mp ?_⟩
    have hsJ : q s ∈ J := by
      change q s ∈ SectionOne.oneJ (V := V) (Sbar : Subgroup X)
      rw [hJid, ← hEid]
      exact ⟨Subgroup.mem_map_of_mem q hs.1, hs.2⟩
    exact hwJ ⟨q s, hsJ⟩
  have hUQ : (Sbar : Subgroup X) ⊓ D ≤ T.map q := by
    intro d hd
    obtain ⟨s, hs, hsd⟩ := hd.1
    refine ⟨s, ⟨hs, (hfix_iff s).mp ?_⟩, hsd⟩
    rw [hsd]
    exact hwD ⟨d, hd.2⟩
  have hDT : ¬ D ≤ T.map q := by
    intro hh
    have hDp := (Sbar.isPGroup'.to_le (Subgroup.map_mono (inf_le_left : T ≤ (S : Subgroup G)))).to_le hh
    have hc := hDp.exists_card_eq
    obtain ⟨n, hn⟩ := hc
    have hsix := SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hD.1
    have hdiv : 3 ∣ 2 ^ n := by rw [← hn, hsix]; decide
    have hbad := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdiv
    norm_num at hbad
  have hTL : T ≤ L := le_inf le_sup_right inf_le_right
  have hDL : D ≤ L.map q := by
    intro d hd
    obtain ⟨g, rfl⟩ := hq d
    refine ⟨g, ⟨(le_sup_left : E ≤ E ⊔ T) (hDE hd), (hfix_iff g).mp (hwD ⟨q g, hd⟩)⟩, rfl⟩
  have hprime : ∀ A B : Subgroup G, T ≤ A → T ≤ B → A ≤ L → B ≤ L →
      D ≤ (A ⊔ B).map q → D ≤ A.map q ∨ D ≤ B.map q := by
    intro A B hTA hTB hAL hBL hsup
    rw [Subgroup.map_sup] at hsup
    apply (SectionOne.sl2_factor_le_sup_iff (Sbar : Subgroup X) Ebar D (T.map q)
      hD.1 hED hQcard hUQ (Subgroup.map_mono inf_le_left)
      (A.map q) (B.map q) (Subgroup.map_mono hTA) (Subgroup.map_mono hTB) ?_ ?_).mp hsup
    · have hm := Subgroup.map_mono (f := q) (hAL.trans inf_le_left)
      rwa [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hq] at hm
    · have hm := Subgroup.map_mono (f := q) (hBL.trans inf_le_left)
      rwa [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hq] at hm
  obtain ⟨F, hTF, hFL, hDF, huniq⟩ := minimal_lift_unique_maximal T L q D hTL hDL hDT hprime
  have hFbig : F ≤ E ⊔ T := hFL.trans inf_le_left
  obtain ⟨P, hP⟩ := sylow_of_normal_sup S E T inf_le_left hSET
  have hTidx : ¬ 2 ∣ T.relIndex F := by
    have hodd : ¬ 2 ∣ T.relIndex (E ⊔ T) := by
      have hsub : T.subgroupOf (E ⊔ T) = (P : Subgroup (↥(E ⊔ T))) := by
        have hm := congrArg (fun A : Subgroup G => A.subgroupOf (E ⊔ T)) hP
        exact hm.symm.trans (subgroupOf_map_subtype_eq _)
      change ¬ 2 ∣ (T.subgroupOf (E ⊔ T)).index
      rw [hsub]
      exact P.not_dvd_index
    intro hdiv
    apply hodd
    have hm := Subgroup.relIndex_mul_relIndex T F (E ⊔ T) hTF hFbig
    rw [← hm]
    exact dvd_mul_of_dvd_left hdiv _
  have hTp : IsPGroup 2 (T.subgroupOf F) := (S.isPGroup'.to_le inf_le_left).comap_of_injective F.subtype F.subtype_injective
  have hTidx' : ¬ 2 ∣ (T.subgroupOf F).index := hTidx
  let TF := hTp.toSylow hTidx'
  have hTFmap : (TF : Subgroup F).map F.subtype = T := by
    dsimp only [TF]
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.map_subgroupOf_eq_of_le hTF
  have hVT : V ≤ T := by
    refine le_inf ((vSubgroup_le_twoCore_and_elementaryAbelian h S).1.trans
      ((pCore_isPGroup (p := 2) (G := G)).le_sylow_of_normal S)) ?_
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := V)).comm (⟨v, hv⟩ : V) w)
  have hVcore : V ≤ twoCoreAmbient F := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (hVT.trans hTF)]
    exact Subgroup.map_mono (show V.subgroupOf F ≤ pCore 2 F from
      le_sSup ⟨Subgroup.normalClosure_normal.subgroupOf F,
        (IsElementaryAbelian.isPGroup 2 V).comap_of_injective F.subtype F.subtype_injective⟩)
  have hcore : twoCoreAmbient F ≠ ⊥ := by
    intro hb
    have hw := hVcore w.property
    rw [hb] at hw
    exact hwne (Subtype.ext hw)
  have hTcore : T ≠ twoCoreAmbient F := by
    intro heq
    have hFnorm : F ≤ Subgroup.normalizer (T : Set G) := by
      rw [heq]
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
      rw [subgroupOf_map_subtype_eq]
      infer_instance
    have hbar : F.map q ≤ Subgroup.normalizer (T.map q : Set X) :=
      (Subgroup.map_mono hFnorm).trans (Subgroup.le_normalizer_map q)
    have hnormD : D ≤ Subgroup.normalizer (((T.map q) ⊓ D : Subgroup X) : Set X) :=
      (le_inf (hDF.trans hbar) D.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hTD : T.map q ⊓ D = (Sbar : Subgroup X) ⊓ D :=
      le_antisymm (inf_le_inf_right _ (Subgroup.map_mono inf_le_left)) (le_inf hUQ inf_le_right)
    rw [hTD] at hnormD
    exact SectionOne.sl2_not_normalizes_order_two D _ hD.1 hQcard inf_le_right hnormD
  exact ⟨F, ⟨⟨hFbig, ⟨TF, hTFmap⟩, hcore, hTcore⟩, huniq⟩, hDF, hFL.trans inf_le_right⟩

end Stellmacher.SectionTwo


module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRemainingCarriers
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.SolvableCubics
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.SolvableCubics
public import Theory.GroupTheory.SolvableSylowOvergroups.CubicControl

/-!
# Excluding the HS and Rudvalis containing quotients

The same selected container already forces the original residual quotient
PSL₂(4) and the right Hall order three. Keep that cubic and both original
Hall factors in the solvable Borel-intersection product. Its image in
Y/O₂(Y) has the full original Sylow. The native HS and Rudvalis local
quotient maps bound the odd part of a solvable full-Sylow overgroup
containing this cubic by three.

The odd outer action is trivial. Consequently the inner image of the
whole odd Hall product equals the right cubic image; its kernel centralizes
the same container. This forces normalization of the actual residual
image, and the checked perfect-residual lifting theorem gives normalization
upstairs, contradicting the original escape. Rudvalis simplicity is
inherited from the selected A.3.6 simple image, not a new model assumption.

The exhaustive reduction retains M₂₄, Held, both genuine nonquasisimple
alternatives and the complete binary-triality endpoint. It preserves the
original W, Sylow, relative normality and literal quotient maps. Their
exclusions and full SourceLocalCartanEscape remain with this owner.
Source: Aschbacher--Smith 5.1.12--13 and A.3.12(18,20), printed
pp.635--638,47--48, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

private theorem odd_normalizes_sparse_section
    (C R J E B : Subgroup G) [C.Normal] [Group.IsSolvable J]
    [IsSimpleGroup C] [Group.IsPerfect C]
    (hm : Nonempty (C ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (C ≃* Rudvalis.Model)) (hRC : R ≤ C)
    (S : Sylow 2 G) (hSJ : (S : Subgroup G) ≤ J) (hEJ : E ≤ J)
    (hBE : B ≤ E) (hBR : B ≤ R) (hB : Nat.card B = 3)
    (hodd : Odd (Nat.card E)) : E ≤ normalizer (R : Set G) := by
  have branch {X : Type} [Group X] [Finite X] [Nontrivial X] (e : C ≃* X)
      (hzX : center X = ⊥) (hoX : IsPGroup 2 (MulAut.Outer X))
      (hnative : ∀ (P : Sylow 2 X) (M N : Subgroup X), (P : Subgroup X) ≤ M →
        M ≠ ⊤ → Group.IsSolvable M → 3 ∣ Nat.card M → N ≤ M →
        Odd (Nat.card N) → Nat.card N ∣ 3) : E ≤ normalizer (R : Set G) := by
    have hz : center C = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hh := (centerCongr e ⟨x,hx⟩).property
      change e x ∈ center X at hh
      rw [hzX,mem_bot] at hh
      exact e.map_eq_one_iff.mp hh
    apply odd_normalizes_of_cubic_sylow_overgroups C R J E B hz
      (hoX.of_equiv (MulAut.outerCongr e).symm) _ hRC S hSJ hEJ hBE hBR hB hodd
    intro P M N hPM hs h3 hNM ho
    let := hs
    let Mm := M.map e.toMonoidHom
    let Nm := N.map e.toMonoidHom
    let : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let : Group.IsSolvable Mm := Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective M)
    have hMt : Mm ≠ ⊤ := by
      intro ht
      let : Group.IsSolvable X := Group.isSolvable_of_surjective
        (f := Mm.subtype) (by rw [ht]; exact topEquiv.surjective)
      exact Group.IsPerfect.not_isSolvable X inferInstance
    have hd := hnative (P.mapSurjective (f := e.toMonoidHom) e.surjective) Mm Nm
      (map_mono hPM) hMt inferInstance (by rwa [card_map_of_injective e.injective])
      (map_mono hNM) (by rwa [card_map_of_injective e.injective])
    rwa [card_map_of_injective e.injective] at hd
  rcases hm with he | he
  · obtain ⟨e⟩ := he
    let : IsSimpleGroup Sporadic.LeechRelated.HS.Carrier := e.symm.isSimpleGroup
    exact branch e Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot
      (Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
        Sporadic.LeechRelated.HS.pointStabilizer_map
        Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow)
      Sporadic.LeechRelated.HS.SylowOvergroups.odd_card_dvd_three_of_cubic
  · obtain ⟨e⟩ := he
    let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
    let : Group.IsPerfect Rudvalis.Model := Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom) e.surjective
    have hO : pCore 2 Rudvalis.Model = ⊥ := by
      apply (inferInstance : (pCore 2 Rudvalis.Model).Normal).eq_bot_or_eq_top.resolve_right
      intro ht
      have hp : IsPGroup 2 Rudvalis.Model := by
        have hh := pCore_isPGroup (p := 2) (G := Rudvalis.Model)
        rw [ht] at hh
        exact hh.of_equiv topEquiv
      let : Group.IsNilpotent Rudvalis.Model := hp.isNilpotent
      exact Group.IsPerfect.not_isSolvable Rudvalis.Model inferInstance
    exact branch e Rudvalis.LowCentralizers.model_center_eq_bot Rudvalis.outer_isPGroup_two
      (Rudvalis.SylowOvergroups.odd_card_dvd_three_of_cubic
        (ChapterF.Source.RudvalisLocal.sylow_overgroup_cover hO))

/-- The original escaping configuration cannot have the HS or Rudvalis containing quotient. -/
theorem not_higmanSims_rudvalis_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hsimple : IsSimpleGroup (C.map (QuotientGroup.mk' (pCore 2 Y)))) :
    ¬ (Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Rudvalis.Model)) := by
  intro he
  obtain ⟨hKR,_,hBc⟩ := higmanSims_rudvalis_residual_and_hall
    h hH hgen c hK hKT horbit hY hescape C hC hKC he
  have hRC : residual H ≤ C.map Y.subtype := hKR ▸ hKC
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype hTY
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  let Abar := (A.subgroupOf Y).map q
  let Bbar := (B.subgroupOf Y).map q
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hle : Rbar ≤ Cbar := map_mono hRC'
  have hBbar : Nat.card Bbar = 3 := by
    have hd : Nat.card Bbar ∣ 3 := by
      have hd := card_map_dvd (B.subgroupOf Y) q
      rwa [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,hBc] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hb | hb
    · have hz : Bbar = ⊥ := eq_bot_of_card_eq _ hb
      have hle : B.subgroupOf Y ≤ pCore 2 Y := by
        simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
      obtain ⟨k,hk⟩ := (pCore_isPGroup.to_le hle).exists_card_eq
      rw [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,hBc] at hk
      have hh : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (by rw [←hk])
      norm_num at hh
    · exact hb
  have hBA : Bbar ≤ normalizer (Abar : Set (Y ⧸ pCore 2 Y)) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    intro b hb
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (c.right_normalizes_left hb) (a : G)
  have hoddA : Odd (Nat.card Abar) := by
    have hoA : Odd (Nat.card A) := by
      rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
      exact OddHall.odd_hall_odd c.left_hall
    have hoAY : Odd (Nat.card (A.subgroupOf Y)) := by
      rw [←inf_subgroupOf_right A Y,Nat.card_congr
        (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
      exact hoA.of_dvd_nat (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
    exact hoAY.of_dvd_nat (card_map_dvd _ q)
  let E := Abar ⊔ Bbar
  have hoddE : Odd (Nat.card E) := by
    have hh := hoddA.mul (show Odd (Nat.card Bbar) by rw [hBbar]; decide)
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes Abar Bbar hBA] at hh
    exact hh.of_dvd_nat (dvd_mul_left _ _)
  have hLH : ¬ L ≤ H := by
    intro hh
    exact hescape (inf_le_left.trans ((c.left_le.trans (inf_le_left.trans hh)).trans
      (le_normalizer_residual H)))
  have prep := cartanPreparation_of_not_le h hH hgen hLH
  let M := normalizer (L : Set G) ⊓ H
  let V := localBorel T L ⊔ M
  let : Group.IsSolvable (localBorel T L) := prep.borel_solvable
  let : Group.IsSolvable M := prep.intersection_solvable
  let : Group.IsSolvable V := Group.isSolvable_sup_of_normalizes _ _ prep.intersection_normalizes
  let JY := (A.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y) ⊔ B.subgroupOf Y
  have hJV : JY.map Y.subtype ≤ V := by
    rw [Subgroup.map_sup,Subgroup.map_sup,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hTY,
      map_subgroupOf_eq_of_le hBY]
    exact sup_le (sup_le ((inf_le_left.trans c.left_le).trans le_sup_left)
      ((le_inf h.sylow_normalizes hH.1.1.2).trans le_sup_right))
      (c.right_le.trans le_sup_right)
  let : Group.IsSolvable JY := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hJV).comp
      (JY.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
    ((inclusion_injective hJV).comp (JY.equivMapOfInjective Y.subtype Y.subtype_injective).injective)
  let J := JY.map q
  let : Group.IsSolvable J := Group.isSolvable_of_surjective (q.subgroupMap_surjective JY)
  let : Cbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup Cbar := hsimple
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  let : Group.IsPerfect Cbar := (hC.map_quotient (pCore 2 Y)).perfect
  have hnorm := odd_normalizes_sparse_section Cbar Rbar J E Bbar
    (he.imp (fun hm => hm.map (fun e => (cComponentTwoCoreQuotientEquiv hC).symm.trans e))
      (fun hm => hm.map (fun e => (cComponentTwoCoreQuotientEquiv hC).symm.trans e))) hle P
    (map_mono (show (T : Subgroup G).subgroupOf Y ≤ JY from le_sup_right.trans le_sup_left))
    (sup_le (map_mono (le_sup_left.trans le_sup_left)) (map_mono le_sup_right))
    le_sup_right (map_mono (comap_mono (Global.right_cartan_le_residual c))) hBbar hoddE
  exact hescape ((residual_escape_twoCore_iff h.qtke h.sylow_normalizes hH hgen hY.2).mp
    (le_sup_left.trans hnorm))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Exclude both sparse sporadic rows on the same selected container,
retaining the full binary endpoint and both nonquasisimple alternatives. -/
theorem localCartan_escape_nonsparse_carriers
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    (n = 2 ∧ CartanExceptionalConclusion T L W H) ∨
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ C.Normal ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        let I := C.map (QuotientGroup.mk' (pCore 2 Y))
        A36Common I ∧
          ((K = residual H ∧ C.Normal ∧
            Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
            n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
            localBorel T L ≤ omegaCentralizer T ∧
            IsOneOrTwoA5Modules L (layer L W) ∧ Nat.card B = 7 ∧
            B ≤ centralizer
              (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∨
          (IsSimpleGroup I ∧
            (Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M24) ∨
              Nonempty ((C ⧸ pCore 2 C) ≃* Held.He))) ∨
          A36Natural I ∨ A36Nilpotent I) := by
  rcases localCartan_escape_remaining_carriers h hH hgen c hY hescape with hout |
    ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hCn,hKC,hlt,hn,hqlt,hcommon,halt⟩
  · exact .inl hout
  · let := hCn
    refine .inr ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hCn,hKC,hlt,hn,hqlt,hcommon,?_⟩
    rcases halt with hbin | ⟨hs,hm⟩ | hnat | hnil
    · exact .inl hbin
    · rcases hm with hM | hHe | ⟨hsparse,_⟩
      · exact .inr (.inl ⟨hs,.inl hM⟩)
      · exact .inr (.inl ⟨hs,.inr hHe⟩)
      · exact (LocalSieve.not_higmanSims_rudvalis_container h hH hgen c hKL hKT hR
          hY hescape C hC hKC hs hsparse).elim
    · exact .inr (.inr (.inl hnat))
    · exact .inr (.inr (.inr hnil))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

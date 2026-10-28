module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMathieuCoverResidual
public import Theory.GroupTheory.InnerImageGeometry
public import Theory.GroupAction.CubicCenterRankTwo

/-!
# Excluding the central M₂₂ cover in the original local Cartan sieve

The original residual and right Hall quotient are identified in the companion
module. Central Sylow transfer shows that the right cubic remains faithful
in the inner action: the perfect residual has no factor nine in its order.
For the same C/O₂(C), the inner automorphism group is the actual M₂₂ carrier.
The original solvable Cartan--Sylow join contains its full inner Sylow, so
native M₂₂ local geometry forces the odd image into the right Hall image.
This normalizes the residual image, contradicting the proved perfect lift
of the original Cartan escape.

The proof retains the cubic center, both Hall conditions, the original
Sylow and literal action maps. It excludes a covering row, without assuming
that the containing quotient is simple or that its two-core is trivial.
Source: Aschbacher--Smith 5.1.13, printed pp.636--637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem odd_normalizes_mathieu_section_of_inner_sylow
    (C R J E B : Subgroup G) [C.Normal] [Group.IsSolvable J]
    (eC : C ≃* Sporadic.Mathieu.M22) (hRC : R ≤ C)
    (P : Sylow 2 C) (hPJ : (P : Subgroup C).map C.subtype ≤ J) (hEJ : E ≤ J)
    (hBE : B ≤ E) (hBR : B ≤ R) (hB : Nat.card B = 3)
    (hodd : Odd (Nat.card E)) : E ≤ normalizer (R : Set G) := by
  let f : G →* MulAut C := MulAut.conjNormal
  let i : C →* MulAut C := MulAut.conj
  have hz : center C = ⊥ := by
    apply bot_unique
    intro z hz
    have hh : eC z ∈ center Sporadic.Mathieu.M22 :=
      (centerCongr eC ⟨z,hz⟩).property
    rw [Sporadic.Mathieu.m22_center_eq_bot,mem_bot] at hh
    exact eC.injective (hh.trans eC.map_one.symm)
  have hi : Function.Injective i := conj_injective_of_center_eq_bot hz
  have hfi (x : C) : f x = i x := by ext y; rfl
  have houter : IsPGroup 2 (MulAut.Outer C) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [pow_one,Nat.card_congr (MulAut.outerCongr eC).toEquiv]
    exact Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two
  have hEin : E.map f ≤ i.range := by
    let q := QuotientGroup.mk' (MulAut.innerSubgroup C)
    have hod : Odd (Nat.card ((E.map f).map q)) :=
      hodd.of_dvd_nat ((card_map_dvd _ q).trans (card_map_dvd _ f))
    obtain ⟨k,hk⟩ := (houter.to_subgroup ((E.map f).map q)).exists_card_eq
    have hk0 : k = 0 := by
      by_contra hk0
      exact hod.not_two_dvd_nat (by rw [hk]; exact dvd_pow_self 2 hk0)
    have hb : (E.map f).map q = ⊥ := card_eq_one.mp (by rw [hk,hk0,pow_zero])
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hb
  let M := (J.map f).comap i
  let N := (E.map f).comap i
  have hNmap : N.map i = E.map f := map_comap_eq_self hEin
  have hNc : Nat.card N = Nat.card (E.map f) := by
    rw [←hNmap,card_map_of_injective hi]
  have hNM : N ≤ M := comap_mono (map_mono hEJ)
  let : Group.IsSolvable (J.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
  let : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
    (f := i.subgroupComap (J.map f)) (fun x y he => Subtype.ext (hi (congrArg Subtype.val he)))
  have hPM : (P : Subgroup C) ≤ M := by
    intro x hx
    change i x ∈ J.map f
    rw [←hfi]
    exact mem_map_of_mem f (hPJ (mem_map_of_mem C.subtype hx))
  have hfB : Function.Injective (f.comp B.subtype) := by
    intro x y hh
    have he (b : B) : f (b : G) = i (inclusion (hBR.trans hRC) b) :=
      hfi (inclusion (hBR.trans hRC) b)
    change f (x : G) = f (y : G) at hh
    rw [he x,he y] at hh
    exact inclusion_injective (hBR.trans hRC) (hi hh)
  have hBc : Nat.card (B.map f) = 3 := by
    rw [←range_subtype B,←MonoidHom.range_comp]
    exact (Nat.card_congr (MonoidHom.ofInjective hfB).toEquiv).symm.trans hB
  have h3M : 3 ∣ Nat.card M := by
    have hd := card_dvd_of_le (map_mono (f := f) hBE)
    rw [hBc,←hNc] at hd
    exact hd.trans (card_dvd_of_le hNM)
  have hMc : Nat.card M = 384 := by
    let Mm := M.map eC.toMonoidHom
    have hn : (Mm.subgroupOf Mm).Normal := by rw [subgroupOf_self]; infer_instance
    let : Group.IsSolvable Mm := Group.isSolvable_of_surjective (eC.toMonoidHom.subgroupMap_surjective M)
    have hh := Sporadic.Mathieu.M22SolvableSylow.card_eq_384_of_solvable_normal_three
      Mm Mm le_rfl hn inferInstance (by rwa [card_map_of_injective eC.injective])
      ⟨P.mapSurjective (f := eC.toMonoidHom) eC.surjective,map_mono hPM⟩
    rwa [card_map_of_injective eC.injective] at hh
  have hsmall : Nat.card (E.map f) ≤ 3 := by
    have hoN : Odd (Nat.card N) := by rw [hNc]; exact hodd.of_dvd_nat (card_map_dvd _ f)
    have hd : Nat.card N ∣ 3 * 128 := by simpa only [hMc] using card_dvd_of_le hNM
    have hc : Nat.Coprime (Nat.card N) 128 := hoN.coprime_two_right.pow_right 7
    rw [←hNc]
    exact Nat.le_of_dvd (by decide) (hc.dvd_of_dvd_mul_right hd)
  have he : B.map f = E.map f := eq_of_le_of_card_ge (map_mono hBE) (by rw [hBc]; exact hsmall)
  intro x hx
  obtain ⟨b,hb,hbx⟩ := mem_map.mp (he.symm ▸ mem_map_of_mem f hx)
  have hker : x * b⁻¹ ∈ f.ker := by
    change f (x * b⁻¹) = 1
    rw [map_mul,map_inv,hbx,mul_inv_cancel]
  have hc : x * b⁻¹ ∈ centralizer (C : Set G) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact hker
  have hn := (centralizer_le hRC).trans (centralizer_le_normalizer (R : Set G)) hc
  simpa only [inv_mul_cancel_right] using
    (normalizer (R : Set G)).mul_mem hn (R.le_normalizer (hBR hb))

/-- The original Cartan intersection cannot escape in a central triple
cover of M₂₂. The right cubic and residual marking are derived here. -/
theorem not_mathieu_cover_container
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
    (hKC : K ≤ C.map Y.subtype) :
    ¬ IsM22Cover (C ⧸ pCore 2 C) := by
  intro hm
  obtain ⟨hKR,hfour,hBc⟩ := normal_mathieu_cover_residual_and_hall
    h hH hgen c hK hKT horbit hY hescape C hC hKC hm
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  have hBY := (Global.right_cartan_le_residual c).trans hRY
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) (hKR ▸ hKC)
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hBC : B.subgroupOf Y ≤ C :=
    (comap_mono (Global.right_cartan_le_residual c)).trans hRC
  let Q := C ⧸ pCore 2 C
  let q := QuotientGroup.mk' (pCore 2 C)
  let f := normalQuotientAction C (pCore 2 C)
  let R := ((residual H).subgroupOf Y).map f
  let D := (A.subgroupOf Y).map f
  let B₀ := (B.subgroupOf Y).map f
  let I := MulAut.innerSubgroup Q
  let RC := ((residual H).subgroupOf Y).subgroupOf C
  let BC := (B.subgroupOf Y).subgroupOf C
  let er := (subgroupOfEquivOfLe hRC).trans (subgroupOfEquivOfLe hRY)
  let eb := (subgroupOfEquivOfLe hBC).trans (subgroupOfEquivOfLe hBY)
  have hBC3 : Nat.card BC = 3 := (Nat.card_congr eb.toEquiv).trans hBc
  have ha : MulAut.conj.comp q = f.comp C.subtype := by
    apply MonoidHom.ext
    intro x
    exact (normalQuotientAction_inner C (pCore 2 C) x).symm
  have hBi : (BC.map q).map MulAut.conj = B₀ := by
    rw [map_map,ha,←map_map,map_subgroupOf_eq_of_le hBC]
  have hRi : (RC.map q).map MulAut.conj = R := by
    rw [map_map,ha,←map_map,map_subgroupOf_eq_of_le hRC]
  have hR9 : ¬ 9 ∣ Nat.card (RC.map q) := by
    have hc : Nat.card (residual H ⧸ pCore 2 (residual H)) = 60 := by
      let a := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
      let eq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
      obtain ⟨F,_,_,hF,⟨b⟩⟩ := hfour
      let d := eq.symm.trans (b.trans
        (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)
      rw [Nat.card_congr d.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      norm_num
    intro hd
    have hd' := hd.trans (card_map_dvd RC q)
    rw [Nat.card_congr er.toEquiv,
      card_eq_card_quotient_mul_card_subgroup (pCore 2 (residual H)),hc] at hd'
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := residual H)).exists_card_eq
    rw [hk] at hd'
    have he : 9 ∣ 60 := ((by decide : Nat.Coprime 9 2).pow_right k).dvd_of_dvd_mul_right hd'
    norm_num at he
  have hBq : Nat.card (BC.map q) = 3 := by
    have hd : Nat.card (BC.map q) ∣ 3 := hBC3 ▸ card_map_dvd BC q
    apply ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left
    intro hc
    have hb : BC.map q = ⊥ := card_eq_one.mp hc
    have hle : BC ≤ pCore 2 C := by
      simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hb
    obtain ⟨k,hk⟩ := (pCore_isPGroup.to_le hle).exists_card_eq
    rw [hBC3] at hk
    have hh : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (by rw [←hk])
    norm_num at hh
  let := residual_perfect h.qtke h.sylow_normalizes hH hgen
  let : Group.IsPerfect RC := Group.IsPerfect.ofSurjective
    (f := er.symm.toMonoidHom) er.symm.surjective
  let : Group.IsPerfect (RC.map q) := Group.IsPerfect.map _
  have hB₀ : Nat.card B₀ = 3 := hBi ▸ CubicCenterRankTwo.inner_card_three
    (RC.map q) (BC.map q) hR9
    (map_mono (comap_mono (comap_mono (Global.right_cartan_le_residual c)))) hBq
  obtain ⟨_,hoD,hBD,hes,_,_⟩ := cartan_action_escape h hH hgen c hY hescape C hRC
  let E := D ⊔ B₀
  have hoE : Odd (Nat.card E) := by
    have hh := hoD.mul (show Odd (Nat.card B₀) by rw [hB₀]; decide)
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes D B₀ hBD] at hh
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
  let J := JY.map f
  let : Group.IsSolvable J := Group.isSolvable_of_surjective (f.subgroupMap_surjective JY)
  have hRI : R ≤ I := by rw [←hRi]; exact map_le_range _ _
  let S := T.subtype hTY
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let i : Q →* I := (MulAut.conj : Q →* MulAut Q).rangeRestrict
  have hi : Function.Surjective i := MonoidHom.rangeRestrict_surjective _
  let P₀ := (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))).mapSurjective hi
  have hPJ : ((P₀ : Subgroup I).map I.subtype) ≤ J := by
    rintro _ ⟨x,⟨y,⟨z,hz,rfl⟩,rfl⟩,rfl⟩
    change MulAut.conj (q z) ∈ J
    rw [←normalQuotientAction_inner]
    apply mem_map_of_mem f
    apply mem_sup_left
    apply mem_sup_right
    rw [hP] at hz
    exact hz
  let eI : I ≃* Sporadic.Mathieu.M22 :=
    (innerEquivCentralQuotient (H := Q)).trans hm.2.2.some
  have hN := odd_normalizes_mathieu_section_of_inner_sylow I R J E B₀ eI hRI P₀ hPJ
    (sup_le (map_mono (le_sup_left.trans le_sup_left)) (map_mono le_sup_right))
    le_sup_right (map_mono (comap_mono (Global.right_cartan_le_residual c))) hB₀ hoE
  exact hes (le_sup_left.trans hN)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

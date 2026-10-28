module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSevenAction
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSevenAction
public import Theory.Alternating.SevenCoverCubicLifts
public import Theory.GroupAction.CubicCenterRankTwo
public import Theory.GroupTheory.CoprimeProductIntersection
public import Theory.SpecificGroups.AlternatingSevenSylowNormalizer

/-!
# Excluding the triple A7 cover on the original Cartan container

The actual Cartan intersection with the selected component is cubic.
Its quotient action cannot vanish: coprime permutability would then force
the original escaping action to normalize a full Sylow of A7. The genuine
cover exponent calculation makes its elements cubic before any lift is
chosen. Its inner image is the entire original escaping action.

The right Hall lies in the original residual. That residual is perfect
and its literal PSL2(4) quotient has no factor nine, so central transfer
makes the right cubic's inner action nontrivial. It normalizes the actual
left cubic, hence centralizes it. Independent inner cubic actions and the
cover's cubic center would contradict the inherited three-rank bound.
This excludes the triple cover while retaining the same component, both
Hall conditions, original quotient maps and arbitrary Sylow/module input.

The private seven-point automorphism equivalence is intentionally reused
through `import all` within this source development; its public boundary
is unchanged. Exhaustive component selection and the binary-triality
ambient exclusion remain open in SourceLocalCartanEscape.
Source: Aschbacher--Smith 5.1.13, printed pp.636--637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem normalizes_image_of_trivial_intersection
    {F : Type*} [Group F] (f : G →* F)
    (A P C : Subgroup G) [C.Normal]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card P))
    (hperm : (A : Set G) * P = (P : Set G) * A)
    (hk : A ⊓ C ≤ f.ker) :
    A.map f ≤ normalizer (((P ⊓ C).map f : Subgroup F) : Set F) := by
  have he : ((A ⊔ P) ⊓ C).map f = (P ⊓ C).map f := by
    apply le_antisymm ?_ (map_mono (inf_le_inf_right C le_sup_right))
    rintro _ ⟨x,hx,rfl⟩
    have hx' : x ∈ (↑(A ⊓ C) : Set G) * (↑(P ⊓ C) : Set G) := by
      rw [←set_mul_inter_normal_of_coprime A P C hcop,
        ←coe_sup_of_set_mul_comm A P hperm]
      exact hx
    obtain ⟨a,ha,p,hp,rfl⟩ := hx'
    rw [map_mul,show f a = 1 from hk ha,one_mul]
    exact mem_map_of_mem f hp
  rw [←he]
  apply (map_mono (f := f) ?_).trans (le_normalizer_map f)
  exact le_sup_left.trans ((le_inf (A ⊔ P).le_normalizer
    le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf)

private theorem odd_image_not_normalizes_seven_sylow
    (P : Sylow 2 (alternatingGroup (Fin 7)))
    (D : Subgroup (Equiv.Perm (Fin 7))) (hc : Nat.card D = 3) :
    ¬ D ≤ normalizer ((P : Subgroup _).map (alternatingGroup (Fin 7)).subtype : Set _) := by
  intro hn
  have ha : D ≤ alternatingGroup (Fin 7) := by
    intro x hx
    rw [Equiv.Perm.mem_alternatingGroup]
    have hp : x ^ 3 = 1 := by
      exact congrArg Subtype.val (hc ▸ pow_card_eq_one' (x := (⟨x,hx⟩ : D)))
    rcases Int.units_eq_one_or x.sign with hs | hs
    · exact hs
    · have hh := congrArg Equiv.Perm.sign hp
      simp only [map_pow,map_one,hs] at hh
      norm_num at hh
  have hd : D.subgroupOf (alternatingGroup (Fin 7)) ≤ (P : Subgroup _) := by
    rw [←AlternatingSevenSylow.sylow_normalizer_eq_self P]
    intro x hx
    have hh := hn hx
    rw [←mem_comap,comap_normalizer_eq_of_le_range] at hh
    · simpa only [comap_map_eq_self_of_injective (alternatingGroup (Fin 7)).subtype_injective, Sylow.coe_coe] using hh
    · exact map_le_range _ _
  have hp : IsPGroup 3 (D.subgroupOf (alternatingGroup (Fin 7))) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_congr (subgroupOfEquivOfLe ha).toEquiv,hc,pow_one]
  have hh := hp.disjoint_of_coprime P.isPGroup' (by decide : Nat.Coprime 3 2)
  have hb : D.subgroupOf (alternatingGroup (Fin 7)) = ⊥ :=
    le_bot_iff.mp ((le_inf le_rfl hd).trans hh.le_bot)
  have hh := Nat.card_congr (subgroupOfEquivOfLe ha).toEquiv
  rw [hb,card_bot,hc] at hh
  omega

theorem alternating_seven_cover_cartan_intersection
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
    (hm : IsAlternatingCover (C ⧸ pCore 2 C) 7) :
    Nat.card ((A.subgroupOf Y).subgroupOf C) = 3 ∧
      ((A.subgroupOf Y).subgroupOf C).map
        ((normalQuotientAction C (pCore 2 C)).comp C.subtype) =
      (A.subgroupOf Y).map (normalQuotientAction C (pCore 2 C)) := by
  let f₀ := normalQuotientAction C (pCore 2 C)
  let Q := C ⧸ pCore 2 C
  let : IsQuasisimple Q := hm.1
  let e := hm.2.2.some
  let j : MulAut Q →* Equiv.Perm (Fin 7) :=
    sevenAutEquiv.symm.toMonoidHom.comp (MulAut.centralQuotientAction e)
  have hj : Function.Injective j := sevenAutEquiv.symm.injective.comp
    (MulAut.centralQuotientAction_injective e)
  let f := j.comp f₀
  let q₀ := QuotientGroup.mk' (pCore 2 C)
  let q : C →* alternatingGroup (Fin 7) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center Q)).comp q₀)
  have hq : Function.Surjective q := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hfC (x : C) : f (x : Y) = (q x : Equiv.Perm (Fin 7)) := by
    apply sevenAutEquiv.injective
    change sevenAutEquiv (sevenAutEquiv.symm _) = _
    rw [MulEquiv.apply_symm_apply,normalQuotientAction_inner,MulAut.centralQuotientAction_conj]
    rfl
  let AY := A.subgroupOf Y
  let TY := (T : Subgroup G).subgroupOf Y
  let E := AY.subgroupOf C
  let Dbar := AY.map f₀
  have hDbar : Nat.card Dbar = 3 := alternating_seven_action_card_three
    h hH hgen c hK hKT horbit hY hescape C hC hKC (.inr hm)
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  let i : E →* A :=
    { toFun x := ⟨x.val.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hi : Function.Injective i := by
    intro x y he
    exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) he)))
  have hoE : Odd (Nat.card E) := hoA.of_dvd_nat (card_dvd_of_injective i hi)
  obtain ⟨F,_,_,_,_,⟨a⟩⟩ := c.left_equiv_units h.linear h.sylow_normalizes
  let : IsCyclic A := isCyclic_of_injective a.toMonoidHom a.injective
  let : IsCyclic E := isCyclic_of_injective i hi
  have hqi : Function.Injective (q₀.comp E.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hd : Disjoint E (pCore 2 C) := by
      apply disjoint_of_coprime_natCard
      obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
      rw [hk]
      exact hoE.coprime_two_right.pow_right k
    exact Subtype.ext (disjoint_def.mp hd x.property ((QuotientGroup.eq_one_iff _).mp hx))
  have hcube (x : E) : x ^ 3 = 1 := by
    have hx : f₀ (x.val : Y) ^ 3 = 1 := by
      let y : Dbar := ⟨f₀ (x.val : Y),mem_map_of_mem f₀ x.property⟩
      exact congrArg Subtype.val (hDbar ▸ pow_card_eq_one' (x := y))
    have hz : q₀ x.val ^ 3 ∈ center Q := by
      have hc : MulAut.conj (q₀ x.val ^ 3) = 1 := by
        rw [map_pow,←normalQuotientAction_inner]
        exact hx
      exact mem_center_iff.mpr fun y =>
        ((mul_inv_eq_iff_eq_mul).mp (DFunLike.congr_fun hc y)).symm
    have hh := GLS3.Chapter5.OddCentralCovers.cube_eq_one_of_cube_mem_center
      (pCore_quotient_pCore_eq_bot (G := C) 2) e (q₀ x.val) hz
    apply hqi
    simpa only [map_pow,map_one,MonoidHom.comp_apply,Subgroup.coe_subtype] using hh
  have hEc : Nat.card E = 1 ∨ Nat.card E = 3 := by
    obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
    exact (Nat.dvd_prime Nat.prime_three).mp (hx ▸ orderOf_dvd_of_pow_eq_one (hcube x))
  have hTY := hH.1.1.2.trans hY.2
  let S := T.subtype hTY
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  have heP : (TY ⊓ C : Subgroup Y).map f =
      ((P.mapSurjective hq : Sylow 2 (alternatingGroup (Fin 7))) : Subgroup _).map
        (alternatingGroup (Fin 7)).subtype := by
    rw [←subgroupOf_map_subtype TY C,map_map]
    have hh : f.comp C.subtype = (alternatingGroup (Fin 7)).subtype.comp q := by
      apply MonoidHom.ext; intro x; exact hfC x
    rw [hh,←map_map]
    change ((TY.subgroupOf C).map q).map (alternatingGroup (Fin 7)).subtype = _
    have hp : TY.subgroupOf C = (P : Subgroup C) := hP.symm
    rw [hp]
    rfl
  have hEn : E.map (f₀.comp C.subtype) ≠ ⊥ := by
    intro hbot
    have hk : AY ⊓ C ≤ f.ker := by
      intro x hx
      have hh : f₀ x = 1 := by
        have hm : f₀ x ∈ E.map (f₀.comp C.subtype) :=
          mem_map_of_mem (f₀.comp C.subtype) (show (⟨x,hx.2⟩ : C) ∈ E from hx.1)
        simpa only [hbot,mem_bot] using hm
      change j (f₀ x) = 1
      rw [hh,map_one]
    have hoAY : Odd (Nat.card AY) := by
      change Odd (Nat.card (A.subgroupOf Y))
      rw [←inf_subgroupOf_right A Y,Nat.card_congr
        (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
      exact hoA.of_dvd_nat (card_dvd_of_le inf_le_left)
    have hcop : Nat.Coprime (Nat.card AY) (Nat.card TY) := by
      obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
      change Nat.card TY = 2 ^ k at hk
      rw [hk]
      exact hoAY.coprime_two_right.pow_right k
    have hp : (AY : Set Y) * TY = (TY : Set Y) * AY := by
      simpa using c.image_intersection_permutes_sylow h.sylow_normalizes hTY (MonoidHom.id Y)
    have hn := normalizes_image_of_trivial_intersection f AY TY C hcop hp hk
    rw [heP] at hn
    apply odd_image_not_normalizes_seven_sylow (P.mapSurjective hq) (AY.map f) ?_ hn
    change Nat.card (AY.map (j.comp f₀)) = 3
    rw [←map_map,card_map_of_injective hj]
    exact hDbar
  have hEc3 : Nat.card E = 3 := hEc.resolve_left fun hc =>
    hEn (by rw [card_eq_one.mp hc,Subgroup.map_bot])
  have hle : E.map (f₀.comp C.subtype) ≤ Dbar := by
    rintro _ ⟨x,hx,rfl⟩
    exact mem_map_of_mem f₀ hx
  have hcard : Nat.card (E.map (f₀.comp C.subtype)) = 3 := by
    have hd := card_map_dvd E (f₀.comp C.subtype)
    rw [hEc3] at hd
    exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left
      (fun he => hEn (card_eq_one.mp he))
  exact ⟨hEc3,eq_of_le_of_card_ge hle (by rw [hcard,hDbar])⟩

private theorem cubic_quotient_card (C : Type*) [Group C] [Finite C]
    (D : Subgroup C) (hD : Nat.card D = 3) :
    Nat.card (D.map (QuotientGroup.mk' (pCore 2 C))) = 3 := by
  let q := QuotientGroup.mk' (pCore 2 C)
  have hk : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hi := injective_comp_subtype_of_coprime_ker q hk D
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hD))
  have hh := (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm
  rw [MonoidHom.range_comp,range_subtype] at hh
  exact hh.trans hD

/-- The triple A7 cover is impossible on the original selected container.
The actual cubic intersection is constructed before comparing its inner
image with the original right Hall subgroup. -/
theorem not_alternating_seven_cover
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
    ¬ IsAlternatingCover (C ⧸ pCore 2 C) 7 := by
  intro hm
  obtain ⟨hKR,hRfour,hB3⟩ := normal_alternating_seven_residual_and_hall
    h hH hgen c hK hKT horbit hY hescape C hC hKC (.inr hm)
  obtain ⟨hE3,hEimage⟩ := alternating_seven_cover_cartan_intersection
    h hH hgen c hK hKT horbit hY hescape C hC hKC hm
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) (hKR ▸ hKC)
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hBR := Global.right_cartan_le_residual c
  have hBY := hBR.trans hRY
  have hBC : B.subgroupOf Y ≤ C := (comap_mono hBR).trans hRC
  let Q := C ⧸ pCore 2 C
  let q := QuotientGroup.mk' (pCore 2 C)
  let f := normalQuotientAction C (pCore 2 C)
  let E := (A.subgroupOf Y).subgroupOf C
  let BC := (B.subgroupOf Y).subgroupOf C
  let RC := ((residual H).subgroupOf Y).subgroupOf C
  let er := (subgroupOfEquivOfLe hRC).trans (subgroupOfEquivOfLe hRY)
  let eb := (subgroupOfEquivOfLe hBC).trans (subgroupOfEquivOfLe hBY)
  have hBC3 : Nat.card BC = 3 := (Nat.card_congr eb.toEquiv).trans hB3
  have hEq3 : Nat.card (E.map q) = 3 := cubic_quotient_card C E hE3
  have hBq3 : Nat.card (BC.map q) = 3 := cubic_quotient_card C BC hBC3
  have ha : MulAut.conj.comp q = f.comp C.subtype := by
    apply MonoidHom.ext
    intro x
    exact (normalQuotientAction_inner C (pCore 2 C) x).symm
  have hEi : (E.map q).map MulAut.conj = (A.subgroupOf Y).map f := by
    rw [map_map,ha]
    exact hEimage
  have hBi : (BC.map q).map MulAut.conj = (B.subgroupOf Y).map f := by
    rw [map_map,ha,←map_map,map_subgroupOf_eq_of_le hBC]
  have hEic : Nat.card ((E.map q).map MulAut.conj) = 3 := by
    rw [hEi]
    exact alternating_seven_action_card_three h hH hgen c hK hKT horbit
      hY hescape C hC hKC (.inr hm)
  let := residual_perfect h.qtke h.sylow_normalizes hH hgen
  let : Group.IsPerfect RC := Group.IsPerfect.ofSurjective
    (f := er.symm.toMonoidHom) er.symm.surjective
  let : Group.IsPerfect (RC.map q) := Group.IsPerfect.map _
  have hR9 : ¬ 9 ∣ Nat.card (RC.map q) := by
    have hc : Nat.card (residual H ⧸ pCore 2 (residual H)) = 60 := by
      let a := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
      let eq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
      obtain ⟨F,_,_,hF,⟨b⟩⟩ := hRfour
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
  have hBic := CubicCenterRankTwo.inner_card_three (RC.map q) (BC.map q)
    hR9 (map_mono (comap_mono (comap_mono hBR))) hBq3
  have hn : BC ≤ normalizer (E : Set C) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (c.right_normalizes_left hb) (x.val : G)
  have hnr := (map_mono (f := q) hn).trans (le_normalizer_map q)
  have hZ : Nat.card (center Q) = 3 := by
    rw [Nat.card_congr hm.2.1.some.toEquiv]
    norm_num
  have hrY : primeRank 3 Y ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 Y) pCore_isPGroup]
    exact (Chapter1.Section02.uniqueness_local_quotient_sqtk h.qtke hY.1).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have hr : primeRank 3 Q ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 C) pCore_isPGroup).trans
      ((_root_.primeRank_le_of_injective 3 C.subtype C.subtype_injective).trans hrY)
  have hle := CubicCenterRankTwo.inner_le_of_normalized_cubics (E.map q) (BC.map q)
    hZ hr hEq3 hBq3 hEic hBic hnr
  rw [hEi,hBi] at hle
  exact (cartan_action_escape h hH hgen c hY hescape C hRC).2.2.2.2.2 hle

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

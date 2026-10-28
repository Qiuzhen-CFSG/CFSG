module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Central-cover transport for the seven-component inspection

The quotient action of a perfect group is faithful.  For an arbitrary family of
quotient automorphisms, the image of the upstairs common fixed subgroup is
normal in the full downstairs common fixed subgroup: a lift of a downstairs
fixed element displaces by a central element.  Components therefore map to
components downstairs, and an A₇ or perfect central three-cover remains one of
those two actual models according to its intersection with the quotient center.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance

private theorem fixed_subgroup_map_component_of_central_ker
    {X Q : Type*} [Group X] [Group Q]
    (P : Subgroup (MulAut X)) (q : X →* Q) (rho : MulAut X →* MulAut Q)
    (hq : Function.Surjective q) (hqker : q.ker ≤ center X)
    (hcompat : ∀ (a : MulAut X) (x : X), q (a x) = rho a (q x))
    (L : Subgroup X) (hL : IsComponentIn L (FixedPoints.subgroup P X))
    (hPbar : Subgroup (MulAut Q)) (hPbar_eq : hPbar = P.map rho)
    (hne : L.map q ≠ ⊥) :
    IsComponentIn (L.map q) (FixedPoints.subgroup hPbar Q) := by
  let C := FixedPoints.subgroup P X
  let D := FixedPoints.subgroup hPbar Q
  let E := D.comap q
  have hCE : C ≤ E := by
    intro x hx
    change q x ∈ D
    rw [FixedPoints.mem_subgroup]
    intro y
    obtain ⟨a, ha, hya⟩ := (show (y : MulAut Q) ∈ P.map rho from hPbar_eq ▸ y.property)
    change (y : MulAut Q) (q x) = q x
    rw [← hya]
    rw [← hcompat (a : MulAut X) x]
    have hax := (FixedPoints.mem_subgroup (M := P) (a := x)).mp hx ⟨a, ha⟩
    change (a : MulAut X) x = x at hax
    exact congrArg q hax
  have hEN : E ≤ normalizer (C : Set X) := by
    apply le_normalizer_iff.mpr
    intro x hx k hk
    rw [FixedPoints.mem_subgroup] at hk ⊢
    intro a
    have ha := a.property
    change (a : MulAut X) (x * (k : X) * x⁻¹) = x * (k : X) * x⁻¹
    have hqfix : q ((a : MulAut X) x) = q x := by
      have hxD : q x ∈ D := hx
      have hfix := (FixedPoints.mem_subgroup (M := hPbar) (a := q x)).mp hxD
      have hamem : rho a ∈ hPbar := by
        rw [hPbar_eq]
        exact mem_map_of_mem rho ha
      have := hfix ⟨rho a, hamem⟩
      exact (hcompat (a : MulAut X) x).trans this
    have hxc : (a : MulAut X) x * x⁻¹ ∈ center X := by
      apply hqker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqfix, mul_inv_cancel]
    have hkfix := (FixedPoints.mem_subgroup (M := P) (a := k)).mp hk a
    change (a : MulAut X) k = k at hkfix
    rw [(a : MulAut X).map_mul, (a : MulAut X).map_mul,
      (a : MulAut X).map_inv, hkfix]
    calc
      (a : MulAut X) x * (k : X) * ((a : MulAut X) x)⁻¹ =
          ((a : MulAut X) x * x⁻¹) * (x * (k : X) * x⁻¹) *
            ((a : MulAut X) x * x⁻¹)⁻¹ := by group
      _ = x * (k : X) * x⁻¹ := by
        rw [← mem_center_iff.mp hxc (x * (k : X) * x⁻¹)]
        group
  have hsub : (C.subgroupOf E).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCE).mpr hEN
  have hLE : IsComponentIn L E := hL.of_subnormal hCE hsub.isSubnormal
  let f := q.subgroupComap D
  have hf : Function.Surjective f := q.subgroupComap_surjective_of_surjective _ hq
  have hle : L.map q ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact hCE (hL.1 hx)
  have hmap : (L.subgroupOf E).map f = (L.map q).subgroupOf D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_map_of_mem q hy
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hLE.1 hy⟩, hy, Subtype.ext hxy⟩
  refine ⟨hle, ?_⟩
  rcases hLE.2.map_surjective f hf with hb | hc
  · exfalso
    have hbot : (L.map q).subgroupOf D = ⊥ := hmap.symm.trans hb
    have hh := congrArg (Subgroup.map D.subtype) hbot
    rw [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at hh
    exact hne hh
  · exact hmap ▸ hc

private theorem isSeven_map_center_quotient
    {X : Type*} [Group X] [Finite X]
    {L : Subgroup X} (hL : IsSeven L)
    (q : X →* (X ⧸ center X)) (hq : q = QuotientGroup.mk' (center X)) :
    IsSeven (L.map q) := by
  let r : L →* L.map q := q.subgroupMap L
  have hr : Function.Surjective r := q.subgroupMap_surjective L
  have hqker : q.ker ≤ center X := by rw [hq, QuotientGroup.ker_mk']
  have hrker : r.ker ≤ center L := by
    intro x hx
    have hxq : q (x : X) = 1 := congrArg Subtype.val hx
    have hxZ : (x : X) ∈ center X := hqker (MonoidHom.mem_ker.mpr hxq)
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp hxZ (y : X))
  rcases hL with ha | hc
  · obtain ⟨e⟩ := ha
    have hZ : center L = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      rw [mem_bot]
      have he1 : e x = e 1 := by
        apply Subtype.ext
        have hcz := (centerCongr e ⟨x, hx⟩).property
        have hcenterA : center (alternatingGroup (Fin 7)) = ⊥ :=
          alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 7))
        have hcz' : (e x : alternatingGroup (Fin 7)) ∈
            (⊥ : Subgroup (alternatingGroup (Fin 7))) := hcenterA ▸ hcz
        simpa only [map_one] using congrArg Subtype.val (mem_bot.mp hcz')
      exact e.injective he1
    have hrker0 : r.ker = ⊥ := le_bot_iff.mp (hrker.trans hZ.le)
    have hrinj : Function.Injective r := r.ker_eq_bot_iff.mp hrker0
    let er : L ≃* L.map q := MulEquiv.ofBijective r ⟨hrinj, hr⟩
    exact Or.inl ⟨er.symm.trans e⟩
  · rcases hc with ⟨hqsim, ⟨ec⟩, ⟨eq⟩⟩
    have hcardZ : Nat.card (center L) = 3 := by
      rw [Nat.card_congr ec.toEquiv]
      simp
    rcases @Subgroup.eq_bot_or_eq_top_of_prime_card (center L) _
        (r.ker.subgroupOf (center L)) ⟨hcardZ ▸ Nat.prime_three⟩ with hk | hk
    · have hker0 : r.ker = ⊥ := by
        rw [← map_subgroupOf_eq_of_le hrker, hk, Subgroup.map_bot]
      have hrinj : Function.Injective r := r.ker_eq_bot_iff.mp hker0
      let er : L ≃* L.map q := MulEquiv.ofBijective r ⟨hrinj, hr⟩
      have hqbar : IsQuasisimple (L.map q) :=
        @IsQuasisimple.of_mulEquiv L (L.map q) _ _ er hqsim
      have hzmap : (center L).map er.toMonoidHom = center (L.map q) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact (centerCongr er ⟨y, hy⟩).property
        · intro hx
          have hxL : (x : X ⧸ center X) ∈ L.map q := x.property
          exact ⟨er.symm ⟨x, hxL⟩, (centerCongr er).symm ⟨x, hx⟩ |>.property,
            er.apply_symm_apply ⟨x, hxL⟩⟩
      exact Or.inr ⟨hqbar, ⟨(centerCongr er).symm.trans ec⟩,
        ⟨(QuotientGroup.congr (center L) (center (L.map q)) er hzmap).symm.trans eq⟩⟩
    · have hkerZ : r.ker = center L := by
        have hh := congrArg (Subgroup.map (center L).subtype) hk
        rw [map_subgroupOf_eq_of_le hrker] at hh
        exact hh.trans ((MonoidHom.range_eq_map _).symm.trans (Subgroup.range_subtype _))
      let er : (L ⧸ center L) ≃* L.map q := by
        have er0 := QuotientGroup.quotientKerEquivOfSurjective r hr
        exact (QuotientGroup.quotientMulEquivOfEq hkerZ.symm).trans er0
      exact Or.inl ⟨er.symm.trans eq⟩

private theorem seven_map_ne_bot_of_component
    {X : Type*} [Group X] [Finite X]
    {L C : Subgroup X} (hL : L ≤ C) (hcomp : IsComponent C (L.subgroupOf C))
    (hs : IsSeven L) (q : X →* (X ⧸ center X)) (hq : q = QuotientGroup.mk' (center X)) :
    L.map q ≠ ⊥ := by
  intro hbot
  have hLp : Group.IsPerfect L := by
    rcases hs with ha | hc
    · obtain ⟨e⟩ := ha
      have hA : Group.IsPerfect (alternatingGroup (Fin 7)) :=
        ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
      exact @Group.IsPerfect.ofSurjective (alternatingGroup (Fin 7)) L _ _
        e.symm.toMonoidHom hA e.symm.surjective
    · exact ⟨hc.1.commutator_eq_top⟩
  have hLcenter : L ≤ center X := by
    apply @Subgroup.perfect_le_of_map_le_of_central_kernel X (X ⧸ center X) _ _ q
      (by rw [hq, QuotientGroup.ker_mk']) L (center X) hLp
    rw [hbot]
    exact bot_le
  have hlin : IsComponentIn L C := ⟨hL, hcomp⟩
  have hntr : Nontrivial L := (nontrivial_iff_ne_bot L).mpr hlin.ne_bot
  have hcomm : IsMulCommutative L := by
    constructor
    constructor
    intro x y
    apply Subtype.ext
    exact (mem_center_iff.mp (hLcenter x.property) (y : X)).symm
  exact @Group.IsPerfect.not_isMulCommutative L _ hntr hLp hcomm

/-- Theorem C's seven-component inspection descends from the actual central quotient. -/
theorem sevenActionInspection_of_quotient_center
    {X : Type*} [Group X] [Finite X] [IsQuasisimple X]
    (hi : SevenActionInspection (X ⧸ center X)) : SevenActionInspection X := by
  intro P hp L hL hcomp hs
  let q : X →* (X ⧸ center X) := QuotientGroup.mk' (center X)
  let rho : MulAut X →* MulAut (X ⧸ center X) := (center X).quotientAut
  let Pbar : Subgroup (MulAut (X ⧸ center X)) := P.map rho
  have hPbar : IsPGroup 2 Pbar := hp.map rho
  have hne : L.map q ≠ ⊥ :=
    seven_map_ne_bot_of_component hL hcomp hs q rfl
  have hcompbar : IsComponentIn (L.map q)
      (FixedPoints.subgroup Pbar (X ⧸ center X)) := by
    apply fixed_subgroup_map_component_of_central_ker P q rho
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
      (fun a x => by
        simpa [q, rho] using (Subgroup.quotientAut_apply_mk (center X) a x).symm)
      L ⟨hL, hcomp⟩ Pbar rfl hne
  have hsbar : IsSeven (L.map q) := isSeven_map_center_quotient hs q rfl
  have hPbot : Pbar = ⊥ := hi Pbar hPbar (L.map q) hcompbar.1 hcompbar.2 hsbar
  apply (P.map_eq_bot_iff_of_injective (MulAut.quotient_center_injective)).mp
  exact hPbot

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance

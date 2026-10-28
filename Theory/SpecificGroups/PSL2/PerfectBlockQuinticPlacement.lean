module

public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.PResidual.InverterPlacement
public import Theory.GroupTheory.PPerfectHom
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.SpecificGroups.PSL2.QuinticTwoPerfect
public import Theory.SpecificGroups.PSL2.QuinticSylowInverter

/-!
# Quintic placement in a perfect linear-two block

A two-perfect subgroup with two-core quotient of order five, normalized by
an actual Sylow subgroup of a perfect PSL₂ cover, either centralizes the
whole cover or is contained in it. The nontrivial action has order five;
its kernel is the whole original two-core. An inverter in the supplied
Sylow then puts the whole subgroup in the cover.

Source: Aschbacher--Smith 6.1.4, printed p.666. This is intrinsic to the
involution-centralizer block and does not identify any ambient core-central
quotient kernel with a two-group.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2

private theorem image_five_quotient {A D : Type*} [_root_.Group A] [_root_.Group D] [Finite A] [Finite D]
    (f : A →* D) (hf : Function.Surjective f) (hp : IsPPerfect 2 A)
    (hfive : Nat.card (A ⧸ pCore 2 A) = 5) (hne : Nat.card D ≠ 1) :
    Nat.card (D ⧸ pCore 2 D) = 5 := by
  have hle : (pCore 2 A).map f ≤ pCore 2 D :=
    le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  let q := QuotientGroup.map (pCore 2 A) (pCore 2 D) f (map_le_iff_le_comap.mp hle)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective _ b
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨QuotientGroup.mk' _ a,rfl⟩
  have hc : Nat.card (D ⧸ pCore 2 D) ∣ 5 := hfive ▸ card_dvd_of_surjective q hq
  rcases (Nat.dvd_prime Nat.prime_five).mp hc with hc | hc
  · have ht : pCore 2 D = ⊤ := index_eq_one.mp hc
    have hD : IsPGroup 2 D := pCore_isPGroup.of_surjective
      ((MulEquiv.subgroupCongr ht).trans topEquiv).toMonoidHom
      ((MulEquiv.subgroupCongr ht).trans topEquiv).surjective
    have hz := hp.hom_eq_one_of_isPGroup hD f
    have hr : (⊤ : Subgroup D) = ⊥ := by
      rw [←f.range_eq_top_of_surjective hf,hz]
      simp
    apply (hne _).elim
    have he := congrArg (fun U : Subgroup D => Nat.card U) hr
    simpa using he
  · exact hc

private theorem kernel_eq_twoCore {A D : Type*} [_root_.Group A] [_root_.Group D]
    [Finite A] [Finite D] (f : A →* D) (hf : Function.Surjective f)
    (hD : Nat.card D = 5) (hA : Nat.card (A ⧸ pCore 2 A) = 5) :
    f.ker = pCore 2 A := by
  have hc : Nat.card ((pCore 2 A).map f) = 1 :=
    ((pCore_isPGroup (p := 2) (G := A)).map f).card_eq_or_dvd.resolve_right (by
      intro hd
      have hh := hd.trans ((pCore 2 A).map f).card_subgroup_dvd_card
      rw [hD] at hh
      norm_num at hh)
  have hb : (pCore 2 A).map f = ⊥ := eq_bot_of_card_eq _ hc
  have hle : pCore 2 A ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp hb
  have hi : f.ker.index = 5 := by
    rw [index_ker,f.range_eq_top_of_surjective hf,card_top,hD]
  have hj : (pCore 2 A).index = 5 := hA
  have hk := f.ker.card_mul_index
  have hc := (pCore 2 A).card_mul_index
  rw [hi] at hk
  rw [hj] at hc
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

private theorem central_action_eq_one {G : Type*} [_root_.Group G]
    (B : Subgroup G) [B.Normal] [Group.IsPerfect B] (x : G)
    (hx : normalQuotientAction B (center B) x = 1) : x ∈ centralizer (B : Set G) := by
  let q := QuotientGroup.mk' (center B)
  have he : (MulAut.conjNormal x : MulAut B).toMonoidHom = MonoidHom.id B := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq q
      (by rw [QuotientGroup.ker_mk'])
    ext b
    have hh := congrArg (fun a : MulAut (B ⧸ center B) => a (q b)) hx
    simpa only [q, normalQuotientAction_apply_mk, MulAut.one_apply,
      MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom] using hh
  intro b hb
  have hh := congrArg Subtype.val (DFunLike.congr_fun he ⟨b,hb⟩)
  change x*b*x⁻¹=b at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Either the whole quintic subgroup lies in the perfect block, or it
centralizes that block. No faithful-action or inverter hypothesis is added. -/
theorem quintic_le_or_centralizes_of_perfect_block
    {G F : Type*} [_root_.Group G] [Finite G] [Field F] [Finite F]
    (B Y : Subgroup G) [B.Normal] [Group.IsPerfect B]
    (U : Sylow 2 B)
    (hUY : (U : Subgroup B).map B.subtype ≤ normalizer (Y : Set G))
    (hY : IsPPerfect 2 Y) (hfive : Nat.card (Y ⧸ pCore 2 Y) = 5)
    {p n : ℕ} (hp : p.Prime) (ho : Odd p) (hn : 0 < n) (hn2 : n ≤ 2)
    (hF : Nat.card F = p^n) (e : B ⧸ center B ≃* PSL(2,F)) :
    Y ≤ B ∨ Y ≤ centralizer (B : Set G) := by
  by_cases hcent : Y ≤ centralizer (B : Set G)
  · exact Or.inr hcent
  left
  let C := B ⧸ center B
  let q := QuotientGroup.mk' (center B)
  let a : G →* MulAut C := normalQuotientAction B (center B)
  let D := Y.map a
  let f : Y →* D := a.subgroupMap Y
  have hf : Function.Surjective f := a.subgroupMap_surjective Y
  have hDp : IsPPerfect 2 D := hY.of_surjective f hf
  have hDne : Nat.card D ≠ 1 := by
    intro hc
    have hb : D = ⊥ := eq_bot_of_card_eq D hc
    apply hcent
    intro y hy
    apply central_action_eq_one B y
    have hh : a y ∈ D := mem_map_of_mem a hy
    rwa [hb,mem_bot] at hh
  have hDfive := image_five_quotient f hf hY hfive hDne
  have houter : IsPGroup 2 (MulAut.Outer C) :=
    (OuterSolvable.SmallDegreeSquares.outer_isPGroup_two hp ho hn2 hF).of_injective
      (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective
  have hinner : D ≤ MulAut.innerSubgroup C := by
    let r : D →* MulAut.Outer C := (QuotientGroup.mk' (MulAut.innerSubgroup C)).comp D.subtype
    have hr := hDp.hom_eq_one_of_isPGroup houter r
    intro d hd
    exact (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun hr ⟨d,hd⟩)
  have hz : center C = ⊥ := by
    apply bot_unique
    intro c hc
    have hh := (centerCongr e ⟨c,hc⟩).property
    change e c ∈ center PSL(2,F) at hh
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hh
    exact e.injective (hh.trans e.map_one.symm)
  let c : C →* MulAut C := MulAut.conj
  have hc : Function.Injective c := Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let R := D.comap c
  have hRD : R.map c = D := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hinner
  let er : R ≃* D := (R.equivMapOfInjective c hc).trans (MulEquiv.subgroupCongr hRD)
  let Rm := R.map e.toMonoidHom
  let em : D ≃* Rm := er.symm.trans (R.equivMapOfInjective e.toMonoidHom e.injective)
  have hpRm : IsPPerfect 2 Rm := hDp.of_surjective em.toMonoidHom em.surjective
  have hRmquot : Nat.card (Rm ⧸ pCore 2 Rm) = 5 := by
    rw [←Nat.card_congr (QuotientGroup.congr _ _ em (pCore_map_iso 2 em)).toEquiv]
    exact hDfive
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) := ⟨p,n,hp,ho,hn,hF⟩
  have hRmcard := (odd_twoPerfect_quintic_subgroup hodd Rm hpRm hRmquot).2
  have hDcard : Nat.card D = 5 := (Nat.card_congr em.toEquiv).trans hRmcard
  have hker := kernel_eq_twoCore f hf hDcard hfive
  let S := U.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hSR : (S : Subgroup C) ≤ normalizer (R : Set C) := by
    rintro z ⟨u,hu,rfl⟩
    apply mem_normalizer_iff.mpr
    intro y
    change c y ∈ D ↔ c (q u*y*(q u)⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    have hh : a (u : G) ∈ normalizer (D : Set (MulAut C)) :=
      Y.le_normalizer_map a (mem_map_of_mem a (hUY (mem_map_of_mem B.subtype hu)))
    rw [show a (u : G) = c (q u) from normalQuotientAction_inner B (center B) u] at hh
    exact mem_normalizer_iff.mp hh (c y)
  let Sm := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hSm : (Sm : Subgroup PSL(2,F)) ≤ normalizer (Rm : Set PSL(2,F)) :=
    (map_mono hSR).trans (R.le_normalizer_map e.toMonoidHom)
  obtain ⟨t,ht,_,htinv⟩ := odd_quintic_sylow_inverter hodd Rm hRmcard Sm hSm
  obtain ⟨s,hs,rfl⟩ := ht
  obtain ⟨u,hu,rfl⟩ := hs
  have hinv (y : G) (hy : y ∈ Y) :
      a (u : G) * a y * (a (u : G))⁻¹ = (a y)⁻¹ := by
    have hyD : a y ∈ R.map c := hRD ▸ mem_map_of_mem a hy
    obtain ⟨r,hr,hra⟩ := hyD
    have hh := htinv (e r) (mem_map_of_mem e.toMonoidHom hr)
    have he : q u*r*(q u)⁻¹=r⁻¹ := by
      apply e.injective
      simpa only [map_mul,map_inv,MulEquiv.coe_toMonoidHom] using hh
    rw [←hra,show a (u : G) = c (q u) from normalQuotientAction_inner B (center B) u]
    simpa only [map_mul,map_inv] using congrArg c he
  apply le_of_normalized_inverter Y B hY (by rw [normalizer_eq_top]; exact le_top) u u.property
  intro y hy
  have hy' : (u : G)*y*(u : G)⁻¹*y ∈ Y :=
    Y.mul_mem ((mem_normalizer_iff.mp (hUY (mem_map_of_mem B.subtype hu)) y).mp hy) hy
  have hfz : f ⟨(u : G)*y*(u : G)⁻¹*y,hy'⟩ = 1 := by
    apply Subtype.ext
    change a ((u : G)*y*(u : G)⁻¹*y)=1
    simp only [map_mul,map_inv]
    rw [hinv y hy,inv_mul_cancel]
  have hkz : (⟨(u : G)*y*(u : G)⁻¹*y,hy'⟩ : Y) ∈ pCore 2 Y := by
    rw [←hker]
    exact hfz
  exact mem_map_of_mem Y.subtype hkz

end Theory.PSL2

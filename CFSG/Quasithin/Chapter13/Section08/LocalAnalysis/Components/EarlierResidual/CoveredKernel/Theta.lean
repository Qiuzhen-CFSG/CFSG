module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.EarlierResidual.Assembly
/-!
# Cubic exclusion in the covered point kernel

Theta(Y) is two-perfect and lies in the literal L₁. A cubic element in
C_Y(V) lies in L₀. Its nontrivial image generates the central marked line
in L₁/O₂(L₁), so theta(Y) has the same image as L₀ or L₁. Uniqueness of
two-perfect lifts recovers equality. The two source normalizer bounds
contradict normality relative to the outside overgroup J.

Source: Aschbacher--Smith 13.3.7--9, printed pp.886--887.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
open Section03.PointResidualImage TransvectionRecognition.Solvable.OneFactor
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ J Y : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)

include d h

omit d h [Finite G] in
private theorem cubicClosure_perfect (Y : Subgroup G) :
    IsPPerfect 2 (closure {x:G | x∈Y ∧ orderOf x=3}) := by
  let D := closure {x:G | x∈Y ∧ orderOf x=3}
  apply (pResidual_eq_top_iff 2 D).mp
  apply map_injective D.subtype_injective
  rw [←MonoidHom.range_eq_map,range_subtype]
  apply le_antisymm (map_subtype_le _)
  apply (closure_le _).mpr
  rintro x ⟨hx,ho⟩
  refine ⟨⟨x,subset_closure ⟨hx,ho⟩⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
  rw [←D.orderOf_coe,ho]
  decide

omit d h [Finite G] in
private theorem cubicClosure_normalized (Y J : Subgroup G)
    (hn : J ≤ normalizer (Y:Set G)) :
    J ≤ normalizer (closure {x:G | x∈Y ∧ orderOf x=3} : Set G) := by
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨(mem_normalizer_iff.mp (hn hg) x).mp hx.1,
    ((MulAut.conj g).orderOf_eq x).trans hx.2⟩

/-- Theta(Y) lies in the literal source L₁ before kernel control is known. -/
theorem covered_theta_placement
    (v : G) (hv : v∈V₁) (hne : v∉V⊓centralizer (L:Set G))
    (hfix : Y ≤ M⊓centralizer ({v}:Set G)) :
    closure {x:G | x∈Y ∧ orderOf x=3} ≤ one L (T:Subgroup G) V₁ := by
  let D := closure {x:G | x∈Y ∧ orderOf x=3}
  have hDY : D ≤ Y := (closure_le _).mpr (fun _ hx => hx.1)
  have hDL : D ≤ L := by
    rw [←theta_normalizer d h]
    exact closure_mono (fun _ hx => ⟨(hfix hx.1).1,hx.2⟩)
  have hv0 : v≠1 := by intro he; exact hne (he ▸ one_mem _)
  have hline : zpowers v = V₁ := by
    have he : zpowers (⟨v,hv⟩:V₁) = ⊤ :=
      zpowers_eq_top_of_prime_card d.line_card (by intro hh; exact hv0 (congrArg Subtype.val hh))
    have hh := congrArg (Subgroup.map V₁.subtype) he
    simpa only [MonoidHom.map_zpowers,subtype_apply,←MonoidHom.range_eq_map,range_subtype] using hh
  have hDC : D ≤ centralizer (V₁:Set G) := by
    rw [←hline,zpowers_eq_closure,centralizer_closure]
    exact hDY.trans (hfix.trans inf_le_right)
  have hDP : D ≤ parabolic L (T:Subgroup G) V₁ :=
    le_inf (hDL.trans le_sup_left) (hDC.trans (Subgroup.centralizer_le_normalizer _))
  have hr : residual D = D := by
    change (pResidual 2 D).map D.subtype = D
    rw [(pResidual_eq_top_iff 2 D).mpr (cubicClosure_perfect Y),
      ←MonoidHom.range_eq_map,range_subtype]
  calc
    D = residual D := hr.symm
    _ ≤ one L (T:Subgroup G) V₁ := embedded_pResidual_mono 2 hDP

omit h in
private theorem eq_zero_or_one_of_cubic_intersection
    (a : NaturalSetup L (T:Subgroup G) V V₁ V₃)
    {D : Subgroup G} (hD : D ≤ one L (T:Subgroup G) V₁)
    (hp : IsPPerfect 2 D) (hn : (T:Subgroup G) ≤ normalizer (D:Set G))
    (x : G) (hx : x∈D) (hz : x∈zero L) (ho : orderOf x=3) :
    D=zero L ∨ D=one L (T:Subgroup G) V₁ := by
  let B := one L (T:Subgroup G) V₁
  have hf := SourceCompletion.CoverFactorization.source_factorization a
  have hzB : zero L ≤ B := zero_le_one_of_factorization L _ V₁ hf
  let C := Source.starImage B D
  let Z := Source.starImage B (zero L)
  have hZ : Nat.card Z = 3 := by
    have hh := (a.marks_card_three hf).1
    rwa [zeroCoreMap,localCoreMap_range] at hh
  let q := QuotientGroup.mk' (pCore 2 B)
  let xb : B := ⟨x,hD hx⟩
  have hxC : q xb ∈ C := ⟨xb,hx,rfl⟩
  have hxZ : q xb ∈ Z := ⟨xb,hz,rfl⟩
  have hx0 : q xb ≠ 1 := by
    intro he
    have hxq : xb∈pCore 2 B := (QuotientGroup.eq_one_iff _).mp he
    have hc := (pCore_isPGroup (p:=2) (G:=B)).orderOf_coprime (by decide : Nat.Coprime 2 3)
      (⟨xb,hxq⟩:pCore 2 B)
    have hh : orderOf (⟨xb,hxq⟩:pCore 2 B)=3 := by
      rw [←(pCore 2 B).orderOf_coe,←B.orderOf_coe]
      exact ho
    rw [hh] at hc
    exact (by decide : ¬Nat.Coprime 3 3) hc
  have hZC : Z ≤ C := by
    have hg : zpowers (⟨q xb,hxZ⟩:Z)=⊤ :=
      zpowers_eq_top_of_prime_card hZ (by intro he; exact hx0 (congrArg Subtype.val he))
    have hh : (zpowers (⟨q xb,hxZ⟩:Z)).map Z.subtype ≤ C := by
      rw [map_le_iff_le_comap]
      exact zpowers_le.mpr hxC
    rwa [hg,←MonoidHom.range_eq_map,range_subtype] at hh
  have hBc : Nat.card (B ⧸ pCore 2 B)=9 := a.one_quotient_card hf
  have hd : Nat.card C ∣ 9 := hBc ▸ C.card_subgroup_dvd_card
  have hle : Nat.card C ≤ 9 := Nat.le_of_dvd (by decide) hd
  have hge : 3 ≤ Nat.card C := hZ ▸ card_le_of_le hZC
  have hposs : Nat.card C=3 ∨ Nat.card C=9 := by
    interval_cases hc : Nat.card C <;> omega
  have hcore : Source.QH B ≤ T := (isPGroup_pCoreIn 2 B).le_sylow_of_normalized T
    ((T_normalizes_one L _ V₁ d.line_stable).trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  rcases hposs with hc | hc
  · left
    apply eq_of_starImage_eq B D (zero L) hD hzB hp (isPPerfect_embedded_pResidual 2 _)
      (hcore.trans hn) ((pCoreIn_le 2 B).trans (one_normalizes_zero L _ V₁ d.normalizes_L))
    exact (eq_of_le_of_card_ge hZC (by rw [hZ,hc])).symm
  · right
    apply eq_of_starImage_eq B D B hD le_rfl hp (isPPerfect_embedded_pResidual 2 _)
      (hcore.trans hn) ((pCoreIn_le 2 B).trans B.le_normalizer)
    change C = Source.starImage B B
    rw [Source.starImage,subgroupOf_self,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact C.eq_top_of_card_eq (hc.trans hBc.symm)

/-- Both genuine normalizer bounds exclude every cubic element in C_Y(V). -/
theorem covered_kernel_no_cubic
    (hc : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hN1 : normalizer (one L (T:Subgroup G) V₁ : Set G) ≤ M)
    (hJ : J ∈ Chapter1.HOutside G (T:Set G) (M:Set G))
    (hYJ : Y ≤ J) (hn : (Y.subgroupOf J).Normal)
    (v : G) (hv : v∈V₁) (hne : v∉V⊓centralizer (L:Set G))
    (hfix : Y ≤ M⊓centralizer ({v}:Set G)) :
    ¬3∣Nat.card (Y⊓centralizer (V:Set G) : Subgroup G) := by
  obtain ⟨a⟩ := covered_flag_of_triple d hc
  have hN0 := SourceCompletion.SolvableSource.covered_normalizer_source d h ⟨a.cover⟩
  let D := closure {x:G | x∈Y ∧ orderOf x=3}
  have hnY := (normal_subgroupOf_iff_le_normalizer hYJ).mp hn
  have hnD := cubicClosure_normalized Y J hnY
  intro hd
  obtain ⟨x,hxo⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have ho : orderOf (x:G)=3 := (Y⊓centralizer (V:Set G)).orderOf_coe x |>.trans hxo
  have hxD : (x:G)∈D := subset_closure ⟨x.property.1,ho⟩
  have hxL : (x:G)∈L := theta_normalizer d h ▸ subset_closure ⟨(hfix x.property.1).1,ho⟩
  have hxP : (x:G)∈centralPreimage L := by
    refine ⟨⟨x,hxL⟩,?_,rfl⟩
    change (⟨x,hxL⟩:L)∈centralCore L
    rw [d.centralCore_eq_centralizer]
    exact x.property.2
  have hxZ : (x:G)∈zero L := by
    refine ⟨⟨x,hxP⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
    rw [←(centralPreimage L).orderOf_coe,ho]
    decide
  rcases eq_zero_or_one_of_cubic_intersection d a
    (covered_theta_placement d h v hv hne hfix) (cubicClosure_perfect Y)
    (hJ.1.2.trans hnD) x hxD hxZ ho with he | he
  · exact hJ.2 (hnD.trans (he ▸ hN0))
  · exact hJ.2 (hnD.trans (he ▸ hN1))
end CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual

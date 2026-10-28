module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Factorization.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.OneFactor.Covered
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Residual.Inputs

/-!
# Covered point-residual recovery in13.3.9

The actual quotient L₁/O₂(L₁) is elementary of order nine, with its two
Sylow-invariant cubic directions marked by L₀ and L₁,+. A two-perfect,
Sylow-normalized subgroup is determined by its image through the original
two-core. Central-kernel control excludes the full nine image; the remaining
nontrivial image is cubic. The outside overgroup excludes L₀ using the genuine
13.2.2(9) normalizer bound. The source factorization proves equality of the
literal barred actions on the original V.

No normality of Y in L₁, abstract chosen cubic model, or split module is assumed.
The preceding placement and central-kernel control remain explicit source inputs.
Source: Aschbacher--Smith13.3.9, p.887;13.2.2(3),(9), pp.877--878.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.PointResidualImage
open Section08
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
open TransvectionRecognition.Solvable.OneFactor
variable {G : Type*} [Group G] [Finite G] {L V V₁ V₃ M J Y : Subgroup G}

omit [Finite G] in
private theorem core_le_sylow (T : Sylow 2 G) (A : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (A : Set G)) : A.pCoreIn 2 ≤ T := by
  have hc : A.pCoreIn 2 ≤ (normalizer (A : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A)
      ((map_subtype_le _).trans A.le_normalizer)
      (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have ht := pCoreIn_le_sylow (normalizer (A : Set G)) (T.subtype hn)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hn] at ht
  exact hc.trans ht

theorem covered_residual_eq_zero_or_plus (T : Sylow 2 G)
    (d : NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hY : Y ≤ one L (T : Subgroup G) V₁) (hp : IsPPerfect 2 Y)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    Y = zero L ∨ Y = plus L (T : Subgroup G) V₁ := by
  let B := one L (T : Subgroup G) V₁
  have hf := SourceCompletion.CoverFactorization.source_factorization d
  have hB : IsPGroup 3 (B ⧸ pCore 2 B) :=
    IsPGroup.of_card (n := 2) (d.one_quotient_card hf)
  let C := Source.starImage B Y
  have hC : pCore 2 C = ⊥ := by
    have hh := IsPGroup.disjoint_of_ne 2 3 (by decide) (pCore 2 C) ⊤
      pCore_isPGroup ((hB.to_subgroup C).to_subgroup ⊤)
    simpa only [disjoint_top] using hh
  have hcard : Nat.card C = 3 := by
    have he := Nat.card_congr (starCoreQuotientEquiv B Y hY).toEquiv
    rw [hC, Nat.card_congr (QuotientGroup.quotientBot).toEquiv] at he
    exact he.symm.trans hc
  have hstable : ∀ t : (T : Subgroup G), ∀ x ∈ C,
      coreAction B ⟨t.val,T_normalizes_one L _ V₁ d.line_stable t.property⟩ x ∈ C := by
    rintro t x ⟨y,hy,rfl⟩
    rw [coreAction_mk]
    refine ⟨B.normalizerMonoidHom
      ⟨t.val,T_normalizes_one L _ V₁ d.line_stable t.property⟩ y,?_,rfl⟩
    exact (mem_normalizer_iff.mp (hn t.property) y.val).mp hy
  have hcore : Source.QH B ≤ T :=
    core_le_sylow T B (T_normalizes_one L _ V₁ d.line_stable)
  rcases d.invariant_marked_line hf C hcard hstable with hz | hx
  · left
    rw [zeroCoreMap,localCoreMap_range] at hz
    exact eq_of_starImage_eq B Y (zero L) hY (zero_le_one_of_factorization L _ V₁ hf)
      hp (isPPerfect_embedded_pResidual 2 _) (hcore.trans hn)
      ((pCoreIn_le 2 B).trans (one_normalizes_zero L _ V₁ d.normalizes_L)) hz
  · right
    rw [plusCoreMap,localCoreMap_range] at hx
    exact eq_of_starImage_eq B Y (plus L (T : Subgroup G) V₁) hY
      (plus_le_one L _ V₁ d.line_stable) hp (isPPerfect_embedded_pResidual 2 _)
      (hcore.trans hn) ((pCoreIn_le 2 B).trans (one_normalizes_plus L _ V₁)) hx

theorem covered_residual_eq_plus_of_outside (T : Sylow 2 G)
    (d : NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hYJ : Y ≤ J) (hp : IsPPerfect 2 Y) (hn : (Y.subgroupOf J).Normal)
    (hY : Y ≤ one L (T : Subgroup G) V₁)
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hz : normalizer (zero L : Set G) ≤ M) : Y = plus L (T : Subgroup G) V₁ := by
  have hnY : J ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYJ).mp hn
  rcases covered_residual_eq_zero_or_plus T d hY hp (hJ.1.2.trans hnY) hc with hzero | hplus
  · exact (hJ.2 (hnY.trans (hzero ▸ hz))).elim
  · exact hplus


/-- The earlier central-kernel control forces the intrinsic cubic quotient;
no cubic-order premise is needed for the nontrivial source subgroup. -/
theorem covered_cubic_or_trivial (T : Sylow 2 G)
    (d : NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hY : Y ≤ one L (T : Subgroup G) V₁) (hp : IsPPerfect 2 Y)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hk : IsPGroup 2 (Y ⊓ centralizer (V : Set G) : Subgroup G)) :
    Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3 := by
  let B := one L (T : Subgroup G) V₁
  have hf := SourceCompletion.CoverFactorization.source_factorization d
  have hBc : Nat.card (B ⧸ pCore 2 B) = 9 := d.one_quotient_card hf
  have hB : IsPGroup 3 (B ⧸ pCore 2 B) := IsPGroup.of_card (n := 2) hBc
  let C := Source.starImage B Y
  have hC : pCore 2 C = ⊥ := by
    have hh := IsPGroup.disjoint_of_ne 2 3 (by decide) (pCore 2 C) ⊤
      pCore_isPGroup ((hB.to_subgroup C).to_subgroup ⊤)
    simpa only [disjoint_top] using hh
  have he : Nat.card (Y ⧸ pCore 2 Y) = Nat.card C := by
    have hh := Nat.card_congr (starCoreQuotientEquiv B Y hY).toEquiv
    rwa [hC, Nat.card_congr (QuotientGroup.quotientBot).toEquiv] at hh
  have hdiv : Nat.card C ∣ 9 := hBc ▸ C.card_subgroup_dvd_card
  have hcore : Source.QH B ≤ T :=
    core_le_sylow T B (T_normalizes_one L _ V₁ d.line_stable)
  have hposs : Nat.card C = 1 ∨ Nat.card C = 3 ∨ Nat.card C = 9 := by
    have hpos := Nat.card_pos (α := C)
    have hle := Nat.le_of_dvd (by decide : 0 < 9) hdiv
    interval_cases h : Nat.card C <;> omega
  rcases hposs with hc | hc | hc
  · left
    have hbot : C = ⊥ := C.eq_bot_iff_card.mpr hc
    exact eq_of_starImage_eq B Y ⊥ hY bot_le hp (by intro N _ _; exact Subsingleton.elim _ _)
      (hcore.trans hn) (by intro x _; rw [mem_normalizer_iff]; intro y; simp)
      (by change C = _; rw [hbot]; simp only [Source.starImage,bot_subgroupOf,Subgroup.map_bot])
  · exact Or.inr (he.trans hc)
  · have htop : C = ⊤ := C.eq_top_of_card_eq (hc.trans hBc.symm)
    have hYB : Y = B := eq_of_starImage_eq B Y B hY le_rfl hp
      (isPPerfect_embedded_pResidual 2 _) (hcore.trans hn)
      ((pCoreIn_le 2 B).trans B.le_normalizer) (by
        change C = Source.starImage B B
        rw [Source.starImage,subgroupOf_self,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
        exact htop)
    have hzB : zero L ≤ B := zero_le_one_of_factorization L _ V₁ hf
    have hzY : zero L ≤ Y ⊓ centralizer (V : Set G) :=
      le_inf (hzB.trans hYB.symm.le) d.zero_centralizes
    have hz2 : IsPGroup 2 (zero L) := hk.of_injective (inclusion hzY) (inclusion_injective hzY)
    have hz2' : IsPGroup 2 (Source.starImage B (zero L)) :=
      (hz2.of_equiv (subgroupOfEquivOfLe hzB).symm).map (QuotientGroup.mk' (pCore 2 B))
    have hzbot : Source.starImage B (zero L) = ⊥ := by
      have hh := IsPGroup.disjoint_of_ne 2 3 (by decide) (Source.starImage B (zero L)) ⊤
        hz2' (hB.to_subgroup ⊤)
      simpa only [disjoint_top] using hh
    have hzcard := (d.marks_card_three hf).1
    rw [zeroCoreMap,localCoreMap_range,hzbot] at hzcard
    simp at hzcard

/-- The marked cubic central residual is invisible on the whole original V. -/
theorem covered_barImage_plus_eq_one (T : Sylow 2 G)
    (d : NaturalSetup L (T : Subgroup G) V V₁ V₃) (hLM : L ≤ M) :
    SolvableExclusion.Residual.barImage M V (plus L (T : Subgroup G) V₁) =
      SolvableExclusion.Residual.barImage M V (one L (T : Subgroup G) V₁) := by
  let P := M ⊓ normalizer (V : Set G)
  have hLP : L ≤ P := le_inf hLM (le_sup_left.trans d.normalizes_V)
  have hp : plus L (T : Subgroup G) V₁ ≤ P :=
    (plus_le_L L _ V₁ d.normalizes_L).trans hLP
  have hz : zero L ≤ P := (zero_le L).trans hLP
  have hzbar : SolvableExclusion.Residual.barImage M V (zero L) = ⊥ := by
    apply bot_unique
    rintro _ ⟨x,hx,rfl⟩
    change _ = 1
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change x.val * v.val * x.val⁻¹ = v.val
    have hcomm : v.val * x.val = x.val * v.val :=
      mem_centralizer_iff.mp (d.zero_centralizes hx) v.val v.property
    rw [← hcomm,mul_inv_cancel_right]
  rw [SourceCompletion.CoverFactorization.source_factorization d]
  unfold SolvableExclusion.Residual.barImage
  rw [subgroupOf_sup hp hz,Subgroup.map_sup]
  change _ = _ ⊔ SolvableExclusion.Residual.barImage M V (zero L)
  rw [hzbar,sup_bot_eq]

/-- The covered native residual supplies every literal 13.3.9 conclusion.
The preceding placement and central-kernel argument supplies hY and hc;
the outside normalizer bound is exactly 13.2.2(9). -/
theorem covered_conclusion_of_placement (T : Sylow 2 G)
    (d : NaturalSetup L (T : Subgroup G) V V₁ V₃) (hLM : L ≤ M)
    (hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hYJ : Y ≤ J) (hp : IsPPerfect 2 Y) (hn : (Y.subgroupOf J).Normal)
    (hY : Y ≤ one L (T : Subgroup G) V₁)
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hz : normalizer (zero L : Set G) ≤ M) :
    SolvableExclusion.Residual.Conclusion1339 L (one L (T : Subgroup G) V₁)
      (plus L (T : Subgroup G) V₁) M V Y := by
  have he := covered_residual_eq_plus_of_outside T d hJ hYJ hp hn hY hc hz
  refine Or.inr ⟨?_,?_,?_,fun _ => he⟩
  · rw [he]
    exact (plus_le_L L _ V₁ d.normalizes_L).trans
      (le_inf hLM (le_sup_left.trans d.normalizes_V))
  · rw [he]
    exact covered_barImage_plus_eq_one T d hLM
  · rintro ⟨e⟩
    have hcard := Nat.card_congr (d.cover.symm.trans e).toEquiv
    rw [Atlas.Codes.hexEven_card,nat_card_alternatingGroup,Nat.card_fin] at hcard
    norm_num at hcard

/-- The native covered branch discharges its cubic-order conclusion from
central-kernel control on the original Y and V. -/
theorem covered_conclusion_of_central_kernel (T : Sylow 2 G)
    (d : NaturalSetup L (T : Subgroup G) V V₁ V₃) (hLM : L ≤ M)
    (hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hYJ : Y ≤ J) (hp : IsPPerfect 2 Y) (hn : (Y.subgroupOf J).Normal)
    (hY : Y ≤ one L (T : Subgroup G) V₁)
    (hk : IsPGroup 2 (Y ⊓ centralizer (V : Set G) : Subgroup G))
    (hz : normalizer (zero L : Set G) ≤ M) :
    SolvableExclusion.Residual.Conclusion1339 L (one L (T : Subgroup G) V₁)
      (plus L (T : Subgroup G) V₁) M V Y := by
  have hnY := (normal_subgroupOf_iff_le_normalizer hYJ).mp hn
  rcases covered_cubic_or_trivial T d hY hp (hJ.1.2.trans hnY) hk with hb | hc
  · exact Or.inl hb
  · exact covered_conclusion_of_placement T d hLM hJ hYJ hp hn hY hc hz
end CFSG.Quasithin.Chapter13.Section03.PointResidualImage

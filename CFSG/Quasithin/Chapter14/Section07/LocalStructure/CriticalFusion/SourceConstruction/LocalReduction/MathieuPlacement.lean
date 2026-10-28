module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.RankTwoComponents
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
public import Theory.GroupTheory.SymmetricThreeTwoCoreCubic

/-!
# The original Mathieu overlap and hexad placement

For a literal M₂₂ component, the rank-two reduction gives I = CT and
L₁ ≤ C. The solvable point residual is normal in C ∩ N_G(L), and its
cubic survives the intrinsic two-core quotient. The native Mathieu
classification places that overlap in a hexad parabolic of order 384.
Both original quotient kernels are two-groups, so I ∩ N_G(L) has order
3·2ⁿ. Its quotient by L₁ is a two-group. Cubic generation of L₁ now
establishes the theta identity required by the existing placement API.

This constructs that API on the original groups, without assuming the
Chapter 13 theta identity for the Chapter 14 flag. All quotient maps,
relative normality, Sylow placement and solvable-overgroup control are
retained for the code contradiction in MathieuExclusion.
Source: Aschbacher–Smith, 14.7.36, printed p.1059, and its cited
13.8.21(2), p.956; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
open Sporadic.Mathieu
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem point_solvable
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Group.IsSolvable (F.Li L 1) := by
  have hc := pointResidual_core_quotient_card (F := F) h structural
  let : IsCyclic ((F.Li L 1) ⧸ pCore 2 (F.Li L 1)) :=
    isCyclic_of_prime_card hc
  let : Group.IsNilpotent (pCore 2 (F.Li L 1)) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (F.Li L 1))).mpr
    ⟨inferInstance,inferInstance⟩

omit [Finite G] in
private theorem overlap_normalizes_point (I : Subgroup G) (hIH : I ≤ F.H) :
    I ⊓ normalizer (L : Set G) ≤ normalizer (F.Li L 1 : Set G) := by
  have hh := ((le_inf (show I ⊓ normalizer (L : Set G) ≤ normalizer (L : Set G) from inf_le_right)
    (inf_le_left.trans (hIH.trans F.H.le_normalizer))).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image (L ⊓ F.H)
          (pResidual 2 (L ⊓ F.H : Subgroup G)))
  have he : F.Li L 1 = (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype := by
    simp only [InvariantFlag.Li,show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,if_false]
    rfl
  rwa [he]

/-- The actual component image of C ∩ N_G(L) is an ordinary hexad parabolic. -/
theorem local_mathieu_native_placement
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I C : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hCI : C ≤ I) (hC : (C.subgroupOf I).IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* M22) :
    ∃ B ∈ m22Blocks,
      Placement.markedImage C (C ⊓ normalizer (L : Set G)) e ≤ MulAction.stabilizer M22 B ∧
      IsCoatom ((Placement.markedImage C (C ⊓ normalizer (L : Set G)) e).subgroupOf
        (MulAction.stabilizer M22 B)) ∧
      m22HexadPointwiseKernel B ≤ Placement.markedImage C (C ⊓ normalizer (L : Set G)) e ∧
      Nat.card (Placement.markedImage C (C ⊓ normalizer (L : Set G)) e) = 384 ∧
      normalizer ((Placement.markedImage C (C ⊓ normalizer (L : Set G)) e).map
        M22ValueBound.Concrete.inclusion : Set m22DesignAut) ≤
          MulAction.stabilizer m22DesignAut B := by
  let eC : C.subgroupOf I ≃* C := subgroupOfEquivOfLe hCI
  let e' := (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).trans e
  obtain ⟨hu,_,_,_,hgen,hLC,_⟩ := local_mathieu_component_eq_residual
    d h hab structural previous faithful earlier I hI (C.subgroupOf I) hC e'
  rw [map_subgroupOf_eq_of_le hCI] at hgen hLC
  let : (C.subgroupOf I).Normal := hC.normal_of_unique hu
  let J := C ⊓ normalizer (L : Set G)
  let X := Placement.markedImage C J e
  let D := Placement.markedImage C (F.Li L 1) e
  have hLJ : F.Li L 1 ≤ J := le_inf hLC
    ((F.Li_le L 1).trans (inf_le_left.trans L.le_normalizer))
  have hDX : D ≤ X := map_mono (comap_mono hLJ)
  have hnorm : (D.subgroupOf X).Normal := by
    have hn : J ≤ normalizer (F.Li L 1 : Set G) :=
      (inf_le_inf_right _ hCI).trans (overlap_normalizes_point I hI.2.1)
    have hnC : J.subgroupOf C ≤ normalizer ((F.Li L 1).subgroupOf C : Set C) :=
      (comap_mono hn).trans (le_normalizer_comap _)
    exact normal_subgroupOf_of_le_normalizer ((map_mono hnC).trans (le_normalizer_map _))
  have hsol : Group.IsSolvable D := by
    let := point_solvable h structural (F := F)
    rw [show D = Placement.markedImage C (F.Li L 1) e from rfl,
      ←Placement.markedMap_range C (F.Li L 1) e hLC]
    exact Group.isSolvable_of_surjective
      (Placement.markedMap C (F.Li L 1) e hLC).rangeRestrict_surjective
  have hthree : 3 ∣ Nat.card D := by
    apply (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mpr
    rw [←Placement.markedImage_three_factorization C (F.Li L 1) e hLC]
    apply (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mp
    have hd := card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 (F.Li L 1)))
      (QuotientGroup.mk'_surjective _)
    rwa [pointResidual_core_quotient_card h structural] at hd
  have hSyl : ∃ S : Sylow 2 M22, (S : Subgroup M22) ≤ X := by
    let S := T.subtype (F.sylow_le_of_mem_Hz hI)
    obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal (C.subgroupOf I)
    let f := (Placement.componentMap C e).comp eC.toMonoidHom
    have hf : Function.Surjective f :=
      (Placement.componentMap_surjective C e).comp eC.surjective
    refine ⟨P.mapSurjective hf,?_⟩
    rintro y ⟨x,hx,rfl⟩
    have hxT : x.val.val ∈ (T : Subgroup G) := by
      rw [hP] at hx
      exact hx
    exact ⟨eC x,⟨x.property,h.sylow_normalizes structural hxT⟩,rfl⟩
  exact M22SolvableSylow.hexad_of_solvable_normal_three X D hDX hnorm hsol hthree hSyl

/-- Two-group kernels retain exactly one factor of three in the full overlap. -/
theorem local_mathieu_overlap_card
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I C : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hCI : C ≤ I) (hC : (C.subgroupOf I).IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* M22) :
    ∃ n : ℕ, Nat.card (I ⊓ normalizer (L : Set G) : Subgroup G) = 3 * 2 ^ n := by
  let eC : C.subgroupOf I ≃* C := subgroupOfEquivOfLe hCI
  let e' := (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).trans e
  obtain ⟨hu,_,_,_,hgen,_,_⟩ := local_mathieu_component_eq_residual
    d h hab structural previous faithful earlier I hI (C.subgroupOf I) hC e'
  rw [map_subgroupOf_eq_of_le hCI] at hgen
  let : (C.subgroupOf I).Normal := hC.normal_of_unique hu
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hs : C.subgroupOf I ⊔ (S : Subgroup I) = ⊤ := by
    rw [Sylow.coe_subtype,←subgroupOf_sup hCI (F.sylow_le_of_mem_Hz hI),hgen,subgroupOf_self]
  have hp : IsPGroup 2 (I ⧸ C.subgroupOf I) :=
    isPGroup_quotient_of_sup_eq_top _ _ S.isPGroup' hs
  let J := I ⊓ normalizer (L : Set G)
  let N := C ⊓ normalizer (L : Set G)
  have hNJ : N ≤ J := inf_le_inf_right _ hCI
  let f : J →* (I ⧸ C.subgroupOf I) :=
    (QuotientGroup.mk' (C.subgroupOf I)).comp (inclusion inf_le_left)
  have hk : f.ker = N.subgroupOf J := by
    ext x
    change QuotientGroup.mk' (C.subgroupOf I) (inclusion inf_le_left x) = 1 ↔
      x.val ∈ N
    exact (QuotientGroup.eq_one_iff _).trans
      ⟨fun hx => ⟨hx,x.property.2⟩,fun hx => hx.1⟩
  obtain ⟨b,hb⟩ := (hp.to_subgroup f.range).exists_card_eq
  have hcJ : Nat.card J = Nat.card N * 2 ^ b := by
    rw [←f.ker.card_mul_index,index_ker,hb,hk,
      Nat.card_congr (subgroupOfEquivOfLe hNJ).toEquiv]
  let g := Placement.markedMap C N e inf_le_left
  obtain ⟨a,ha⟩ := (Placement.markedMap_kernel_isTwoGroup C N e inf_le_left).exists_card_eq
  obtain ⟨B,hB,hX,hmax,hker,hcard,hnorm⟩ := local_mathieu_native_placement
    d h hab structural previous faithful earlier I C hI hCI hC e
  have hcN : Nat.card N = 2 ^ a * 384 := by
    rw [←g.ker.card_mul_index,index_ker,ha,Placement.markedMap_range]
    rw [hcard]
  refine ⟨a + b + 7,?_⟩
  rw [hcJ,hcN,pow_add,pow_add]
  ring

/-- Recover cubic generation in the original overlap from its exact odd part. -/
theorem local_mathieu_point_cubic_closure
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I C : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hCI : C ≤ I) (hC : (C.subgroupOf I).IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* M22) :
    F.Li L 1 = closure {x : G | x ∈ I ⊓ normalizer (L : Set G) ∧ orderOf x = 3} := by
  let J := I ⊓ normalizer (L : Set G)
  let P := (F.Li L 1).subgroupOf J
  have hPJ : F.Li L 1 ≤ J := le_inf (F.Li_one_le_of_mem_Hz hI)
    ((F.Li_le L 1).trans (inf_le_left.trans L.le_normalizer))
  let : P.Normal := normal_subgroupOf_of_le_normalizer (overlap_normalizes_point I hI.2.1)
  obtain ⟨n,hn⟩ := local_mathieu_overlap_card d h hab structural previous faithful earlier
    I C hI hCI hC e
  have hpi : IsPiGroup twoThreePrimes J := by
    apply (IsPiGroup_iff _ _).mpr
    intro p hp
    rw [hn] at hp
    change p.val = 2 ∨ p.val = 3
    rcases p.property.dvd_mul.mp hp with hp | hp
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp hp |>.resolve_left p.property.ne_one)
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (p.property.dvd_of_dvd_pow hp) |>.resolve_left p.property.ne_one)
  have h9 : ¬ 9 ∣ Nat.card J := by
    rw [hn]
    intro hd
    have hc : Nat.Coprime 9 (2 ^ n) := (by decide : Nat.Coprime 9 2).pow_right n
    exact (by decide : ¬ 9 ∣ 3) (hc.dvd_mul_right.mp hd)
  have hthree : 3 ∣ Nat.card P := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv]
    have hd := card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 (F.Li L 1)))
      (QuotientGroup.mk'_surjective _)
    rwa [pointResidual_core_quotient_card h structural] at hd
  have hquot : IsPGroup 2 (J ⧸ P) :=
    isPGroup_two_of_isPiGroup_twoThree (hpi.quotient P) (by
      intro hd
      apply h9
      have hm := Nat.mul_dvd_mul hthree hd
      rwa [←P.index_eq_card,P.card_mul_index] at hm)
  apply le_antisymm
  · let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
    have hB : B ≤ J := sup_le hPJ (le_inf (F.sylow_le_of_mem_Hz hI)
      (h.sylow_normalizes structural))
    rw [←residual_group h structural,
      SymmetricThreeTwoCore.twoResidual_eq_cubic_closure (pointQuotientEquiv h structural),
      MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro x ⟨b,hb,rfl⟩
    exact ⟨hB b.property,(B.orderOf_coe b).trans hb⟩
  · apply (closure_le _).mpr
    rintro x ⟨hx,horder⟩
    have ho : orderOf (⟨x,hx⟩ : J) = 3 := (J.orderOf_coe ⟨x,hx⟩).symm.trans horder
    have hp := mem_pResidual_of_orderOf_coprime (p := 2)
      (show Nat.Coprime 2 (orderOf (⟨x,hx⟩ : J)) from ho ▸ (by decide))
    exact (show pResidual 2 J ≤ P from sInf_le ⟨inferInstance,hquot⟩) hp

/-- All inputs to the native code placement, constructed from the original flag. -/
def localMathieuSetup
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I C : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hCI : C ≤ I) (hC : (C.subgroupOf I).IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* M22) :
    Placement.Setup I C (F.Li L 1) (T : Subgroup G) F.H (normalizer (L : Set G)) := by
  let eC : C.subgroupOf I ≃* C := subgroupOfEquivOfLe hCI
  let e' := (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).trans e
  obtain ⟨hu,_,_,_,hgen,hLC,_⟩ := local_mathieu_component_eq_residual
    d h hab structural previous faithful earlier I hI (C.subgroupOf I) hC e'
  rw [map_subgroupOf_eq_of_le hCI] at hgen hLC
  exact {
    mem_Hz := ⟨⟨hI.1.1,sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)⟩,
      hI.2⟩
    component_le := hCI
    component := hC
    component_normal := hC.normal_of_unique hu
    sylow_le_M := h.sylow_normalizes structural
    sylow := T.subtype (F.sylow_le_of_mem_Hz hI)
    sylow_eq := rfl
    generated := by rw [sup_eq_left.mpr hLC]; exact hgen.symm
    seed_le_component := hLC
    theta := local_mathieu_point_cubic_closure d h hab structural previous faithful earlier
      I C hI hCI hC e
    solvable := point_solvable h structural
    model := e
    solvable_overgroups := fun X hX hB hs =>
      solvable_point_overgroup_le_normalizer d h hab structural previous faithful earlier
        X hX hB hs }

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

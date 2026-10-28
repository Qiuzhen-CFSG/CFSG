module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.ResidualNormalizer
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.InnerRadicalNormalizer
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.IrreducibleSubgroupSize
public import Theory.SpecificGroups.Janko4.Model.SmallMathieuRadicalBound
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.MathieuTwelveSections

/-!
# The original small-Mathieu radical and its faithful module image

Transport the original intersection residual, radical and module through
the containing component's inclusion and its literal central quotient.
The full covering center lies in the radical; the quotient is injective
on the original module. Inner automorphism control transports radical
normalizer containment, while irreducibility descends through these same maps.

The module has order at least 2¹⁰. The M₁₂/M₂₂ quotient bounds the native
radical by 2¹⁵/2¹⁴, forcing all module conjugates in the radical to intersect.
Irreducibility and prime-core centralization then make the entire native
radical centralize the module. The relative indices are at most 32/16;
in the M₁₂ case the residual image also has odd centralizer.

The literal Hall consumer adds these proved constraints to its original
strict full-cover gap and cubic resolution. Its factored-case and gap
witnesses are retained separately. The small-Mathieu pushing-up exclusions
and the full SourceMathieuHallFaithfulAt remain to be proved.

Source: Aschbacher–Smith 4.2.13 and 4.4.14, printed pp.611–612,624–625.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

include D in
theorem sourceOrbit_pushingUp_native_radical
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let U := (J.pCoreIn 2).comap j
    let E := V.comap j
    let B := F.comap j
    q.ker ≤ U ∧ IsPRadical 2 (U.map q) ∧
      normalizer (U.map q : Set Janko4.Model) ≤ normalizer (B.map q : Set Janko4.Model) ∧
      B.map q ≤ normalizer (U.map q : Set Janko4.Model) ∧
      B.map q ≤ normalizer (E.map q : Set Janko4.Model) ∧
      E.map q ≤ U.map q ∧ IsElementaryAbelian 2 (E.map q) ∧
      Nat.card (E.map q) = Nat.card V ∧
      Nonempty (((B.map q) ⧸ pCore 2 (B.map q)) ≃* (L ⧸ pCore 2 L)) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := (J.pCoreIn 2).comap j
  let E := V.comap j
  let B := F.comap j
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hc := hw.2.2.2.2.2.2.1
  let := hK.2
  have hf := sourceOrbit_pushingUp_core_central_product hw K hK e
  have hv := D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK
  have hZ : q.ker ≤ U := by
    rw [hk]
    intro z hz
    exact (hf.2.2.symm.le.trans inf_le_left).trans inf_le_left (mem_map_of_mem j hz)
  have hUr : IsPRadical 2 U := hc.ordinary_radical_intersection_isRadical K hK
  have hUm : (normalizer (U.map q : Set Janko4.Model)).pCoreIn 2 = U.map q :=
    map_normalizer_core_of_p_kernel U hUr.isPGroup hUr.2 q hq hZ
  have hEV : E.map j = V := map_comap_eq_self (hv.1.trans inf_le_right |>.trans_eq hjr.symm)
  let d : E ≃* V := (E.equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hEV)
  let := D.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective d.toMonoidHom d.injective
  let : IsElementaryAbelian 2 (E.map q) := IsElementaryAbelian.map q
  have hi : Function.Injective (q.comp E.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro v hvk
    have hvZ : (v : K) ∈ center K := hk ▸ hvk
    have hvC : j v ∈ centralizer (K.map H.subtype : Set G) := by
      rintro y ⟨y,hy,rfl⟩
      exact congrArg j (mem_center_iff.mp hvZ ⟨y,hy⟩)
    have hvb : j v ∈ (⊥ : Subgroup G) := hv.2 ▸
      ⟨v.property, hv.1 v.property |>.1, hvC⟩
    apply Subtype.ext
    exact hj ((mem_bot.mp hvb).trans (map_one j).symm)
  have hEcard : Nat.card (E.map q) = Nat.card V := by
    have hr : (q.comp E.subtype).range = E.map q := by rw [MonoidHom.range_comp,range_subtype]
    exact (Nat.card_congr ((MonoidHom.ofInjective hi).trans
      (MulEquiv.subgroupCongr hr)).toEquiv).symm.trans (Nat.card_congr d.toEquiv)
  have hEU : E ≤ U := comap_mono hw.2.2.2.2.2.1
  have hne : U.map q ≠ ⊥ := by
    intro hb
    have hEb : E.map q = ⊥ := bot_unique ((map_mono hEU).trans_eq hb)
    have hcE := hEcard
    rw [hEb,card_bot] at hcE
    exact D.ne_bot (card_eq_one.mp hcE.symm)
  have hNu : normalizer (U : Set K) ≤ (H ⊓ normalizer (L : Set G)).comap j := by
    apply hc.ordinary_radical_normalizer_le_local_of_inner K hK
    intro a
    exact Janko4.perfect_cover_conj_surjective e a
  have hFM : F ≤ H ⊓ normalizer (L : Set G) :=
    le_inf ((map_subtype_le _).trans inf_le_right) (((map_subtype_le _).trans inf_le_left).trans L.le_normalizer)
  have hMF : H ⊓ normalizer (L : Set G) ≤ normalizer (F : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hFM).mp hw.2.2.2.2.2.2.2.2.1
  have hNB : normalizer (U : Set K) ≤ normalizer (B : Set K) :=
    (hNu.trans (comap_mono hMF)).trans (F.le_normalizer_comap j)
  have hNU : (normalizer (U : Set K)).map q = normalizer (U.map q : Set Janko4.Model) := by
    have he : (normalizer (U.map q : Set Janko4.Model)).comap q = normalizer (U : Set K) := by
      rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hZ]
    rw [←he,map_comap_eq_self_of_surjective hq]
  have hBnU : B ≤ normalizer (U : Set K) :=
    ((comap_mono ((le_conjugateSpanBy F (H ⊓ normalizer (L : Set G))).trans
      hc.span_normalizes_radical)).trans ((J.pCoreIn 2).le_normalizer_comap j))
  have hBnE : B ≤ normalizer (E : Set K) :=
    (comap_mono (((map_subtype_le _).trans inf_le_left).trans D.normalizes)).trans
      (V.le_normalizer_comap j)
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK := hc.ordinary_component_contains_original K hK
  let b : B ≃* F := (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFH)
  let bq := QuotientGroup.congr (pCore 2 B) (pCore 2 F) b (pCore_map_iso 2 b)
  obtain ⟨ef,_⟩ := hw.2.2.2.2.2.2.2.2.2.2.2.1
  let f := q.subgroupMap B
  have hfp : IsPGroup 2 f.ker := by
    have hZp : IsPGroup 2 (center K) := by
      rw [IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)]
      exact pCore_isPGroup
    have he : f.ker = q.ker.subgroupOf B := by
      ext x
      exact Subtype.ext_iff
    rw [he,hk]
    exact hZp.comap_subtype
  refine ⟨hZ,⟨hne,hUm⟩,?_,(map_mono hBnU).trans (U.le_normalizer_map q),
    (map_mono hBnE).trans (E.le_normalizer_map q),map_mono hEU,inferInstance,hEcard,?_⟩
  · rw [←hNU]
    exact (map_mono hNB).trans (B.le_normalizer_map q)
  · exact ⟨(f.pCoreQuotientEquiv (q.subgroupMap_surjective B) hfp).symm.trans (bq.trans ef)⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open scoped Pointwise IsMulCommutative
variable {G : Type*} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The literal small Mathieu radical has relative index at most 32 or 16
over its original module image; the M12 residual image has odd centralizer. -/
theorem sourceOrbit_pushingUp_small_radical_bounds
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let U := ((J.pCoreIn 2).comap j).map q
    let E := (V.comap j).map q
    let B := (F.comap j).map q
    (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) →
      Nat.card U ≤ 32768 ∧ E.relIndex U ≤ 32 ∧
        ¬ 2 ∣ Nat.card (centralizer (B : Set Janko4.Model))) ∧
    (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22) →
      Nat.card U ≤ 16384 ∧ E.relIndex U ≤ 16) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := ((J.pCoreIn 2).comap j).map q
  let E := (V.comap j).map q
  let B := (F.comap j).map q
  have hn := @sourceOrbit_pushingUp_native_radical G instG finG T L V D hfix A J H W hw K hK e
  dsimp only at hn
  have hUr : IsPRadical 2 U := hn.2.1
  have hBU : B ≤ normalizer (U : Set Janko4.Model) := hn.2.2.2.1
  have hEU : E ≤ U := hn.2.2.2.2.2.1
  have hcard : Nat.card E = Nat.card V := hn.2.2.2.2.2.2.2.1
  let a : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L) := hn.2.2.2.2.2.2.2.2.some
  let z := (centerQuotientCongr a).trans (D.orbitCentralQuotientEquiv h)
  have hk : IsPGroup 2 B.subtype.ker := by
    rw [(MonoidHom.ker_eq_bot_iff B.subtype).mpr B.subtype_injective]
    exact IsPGroup.of_subsingleton 2 _
  have hn : B.subtype.range ≤ normalizer (U : Set Janko4.Model) := by
    rw [range_subtype]
    exact hBU
  have hb := Janko4.small_mathieu_normalized_twoGroup_card_le
    B.subtype hk U hUr.isPGroup hn
  have hcount := (E.subgroupOf U).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hEU).toEquiv] at hcount
  change Nat.card E * E.relIndex U = Nat.card U at hcount
  have hlarge (hm : HasMathieuCentralQuotient D.orbitComponent) : 1024 ≤ Nat.card E := by
    rw [hcard]
    let := D.elementary
    rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) V]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (D.sourceOrbit_mathieu_twoRank_ge_ten hV hm)
  constructor
  · rintro ⟨em⟩
    have hupper := hb.1 ⟨z.trans em⟩
    have hlower := hlarge (.inl ⟨em⟩)
    refine ⟨hupper,by nlinarith,?_⟩
    let f := (z.trans em).toMonoidHom.comp
      ((QuotientGroup.mk' (center (B ⧸ pCore 2 B))).comp (QuotientGroup.mk' (pCore 2 B)))
    exact Janko4.InvolutionCentralizers.m12_section_centralizer_odd B f
      ((z.trans em).surjective.comp
        ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)))
  · rintro ⟨em⟩
    have hupper := hb.2 ⟨z.trans em⟩
    have hlower := hlarge (.inr (.inl ⟨em⟩))
    exact ⟨hupper,by nlinarith⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

include D in
/-- Irreducibility of the original module is retained under the literal native action. -/
theorem sourceOrbit_pushingUp_native_irreducible
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let E := (V.comap j).map q
    let B := (F.comap j).map q
    ∀ X : Subgroup Janko4.Model, X ≤ E → B ≤ normalizer (X : Set Janko4.Model) →
      X = ⊥ ∨ X = E := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let E := V.comap j
  let B := F.comap j
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hc := hw.2.2.2.2.2.2.1
  have hv := D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK
  have hEV : E.map j = V := map_comap_eq_self (hv.1.trans inf_le_right |>.trans_eq hjr.symm)
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK := hc.ordinary_component_contains_original K hK
  have hBF : B.map j = F := by
    apply map_comap_eq_self
    rw [hjr]
    intro f hf
    exact ⟨⟨f,hFH hf⟩,hFK hf,rfl⟩
  have hBE : B ≤ normalizer (E : Set K) :=
    (comap_mono (((map_subtype_le _).trans inf_le_left).trans D.normalizes)).trans
      (V.le_normalizer_comap j)
  apply invariant_subgroup_dichotomy_map q E B hBE
  intro X hXE hBX
  have hXV : X.map j ≤ V := (map_mono hXE).trans_eq hEV
  have hFX : F ≤ normalizer (X.map j : Set G) := by
    rw [←hBF]
    exact (map_mono hBX).trans (X.le_normalizer_map j)
  rcases D.sourceOrbit_residual_invariant_subgroup hfix F (X.map j)
      hw.2.2.2.2.2.2.2.1 hXV hFX with hx | hx
  · exact Or.inl ((X.map_eq_bot_iff_of_injective hj).mp hx)
  · exact Or.inr (map_injective hj (hx.trans hEV.symm))
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open scoped IsMulCommutative
variable {G : Type*} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- In both small-Mathieu rows the entire native radical centralizes the
original nonzero module image. -/
theorem sourceOrbit_pushingUp_small_radical_centralizes
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    ((J.pCoreIn 2).comap j).map q ≤ centralizer ((V.comap j).map q : Set Janko4.Model) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := ((J.pCoreIn 2).comap j).map q
  let E := (V.comap j).map q
  let B := (F.comap j).map q
  have hn := @sourceOrbit_pushingUp_native_radical G instG finG T L V D hfix A J H W hw K hK e
  dsimp only at hn
  have hUr : IsPRadical 2 U := hn.2.1
  have hBU : B ≤ normalizer (U : Set Janko4.Model) := hn.2.2.2.1
  have hBE : B ≤ normalizer (E : Set Janko4.Model) := hn.2.2.2.2.1
  have hEU : E ≤ U := hn.2.2.2.2.2.1
  have hcard : Nat.card E = Nat.card V := hn.2.2.2.2.2.2.2.1
  have hUB : U ≤ normalizer (B : Set Janko4.Model) := U.le_normalizer.trans hn.2.2.1
  have hb := @sourceOrbit_pushingUp_small_radical_bounds G instG finG T L V D
    h hV hfix A J H W hw K hK e
  have hupper : Nat.card U ≤ 32768 := hm.elim (fun he => (hb.1 he).1)
    (fun he => (hb.2 he).1.trans (by decide))
  have hm' : HasMathieuCentralQuotient D.orbitComponent :=
    hm.elim Or.inl (fun he => Or.inr (Or.inl he))
  have hlower : 1024 ≤ Nat.card E := by
    rw [hcard]
    let := D.elementary
    rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) V]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (D.sourceOrbit_mathieu_twoRank_ge_ten hV hm')
  exact le_centralizer_of_large_irreducible E B U hUr.isPGroup hEU hBE hBU hUB
    (@sourceOrbit_pushingUp_native_irreducible G instG finG T L V D hfix A J H W hw K hK e)
    (by nlinarith)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The original nonfaithful Hall subgroup supplies a small native radical
centralizing its faithful module image. The strict full-cover gap and cubic
resolution use the same witnesses throughout. -/
theorem sourceOrbit_mathieu_hall_small_radical
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H₀ : Subgroup G} (hH : H₀ ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H₀)
    (B₀ : Subgroup H₀) (hBN : B₀ ≤ (normalizer (L : Set G)).subgroupOf H₀)
    (hHall : IsHallSubgroup oddPrimes
      (B₀.subgroupOf ((normalizer (L : Set G)).subgroupOf H₀)))
    (hker : B₀.map H₀.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H₀ ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
        Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
      MathieuPushingUpFactoredCase T L V A ∧
      ∃ J H W : Subgroup G, Witness L V A J H W ∧
        ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
          ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
          ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K ∧
          ∃ (e : (K ⧸ center K) ≃* Janko4.Model) (x : K) (r : G),
            orderOf x = 3 ∧ CubicPumpupFullResolution H K x r ∧
            ((T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
              V ⊔ (center K).map (H.subtype.comp K.subtype) < J.pCoreIn 2 ⊓ K.map H.subtype) ∧
            let j := H.subtype.comp K.subtype
            let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
            let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
            let U := ((J.pCoreIn 2).comap j).map q
            let E := (V.comap j).map q
            let B := (F.comap j).map q
            q.ker ≤ (J.pCoreIn 2).comap j ∧ IsPRadical 2 U ∧
              normalizer (U : Set Janko4.Model) ≤ normalizer (B : Set Janko4.Model) ∧
              E ≤ U ∧ Nat.card E = Nat.card V ∧ U ≤ centralizer (E : Set Janko4.Model) ∧
              (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) →
                Nat.card U ≤ 32768 ∧ E.relIndex U ≤ 32 ∧
                  ¬ 2 ∣ Nat.card (centralizer (B : Set Janko4.Model))) ∧
              (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22) →
                Nat.card U ≤ 16384 ∧ E.relIndex U ≤ 16) := by
  have hsource := @sourceOrbit_mathieu_hall_pushingUp_only G instG finG T L V D
    h hmany hV hm hnon H₀ hH hlarge B₀ hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  obtain ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hsmall,hfact,hgap⟩ := hA
  obtain ⟨J,H,W,hw,K,hK,hn,hout,hFK,e,x,r,hx,hfull,hgap⟩ := hgap
  have hfix := (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have hc := @sourceOrbit_pushingUp_native_radical G instG finG T L V D hfix A J H W hw K hK e
  dsimp only at hc
  have hb := @sourceOrbit_pushingUp_small_radical_bounds G instG finG T L V D
    h.toHypothesis1221 hV hfix A J H W hw K hK e
  have hcent := @sourceOrbit_pushingUp_small_radical_centralizes G instG finG T L V D
    h.toHypothesis1221 hV hfix hsmall A J H W hw K hK e
  exact ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hsmall,hfact,
    J,H,W,hw,K,hK,hn,hout,hFK,e,x,r,hx,hfull,hgap,
    hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.2.2.1,hc.2.2.2.2.2.2.2.1,hcent,hb⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48Bridge
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48Source
public import Theory.GroupTheory.PCoreRestriction
public import Theory.ElementaryAbelian.Injective

/-!
# The original binary residual quotient and C.4.8 fixed module

C.2.8 identifies the radical R with O₂(LH R). Restricting this core to
the original intersection residual LH, and using its characteristic
normalization, gives LH ∩ R = O₂(LH). The actual map LH → LH R/R
therefore has exactly this kernel. Its quotient marking is compatible
with the original map into L/O₂(L), and the natural--dual coordinates
retain both marked seed axes and the original conjugator.

For the literal C.4.8 fixed-space commutator W, normality of O₂(LH)
shows that W centralizes this core. The whole doubled source orbit lies
in W and has faithful natural--dual quotient action, so the centralizer
of W inside LH is exactly O₂(LH). Consequently LH R/R acts faithfully
on this same elementary W, with its action formula proved on every
ambient representative. The native-witness application is in C48Native.

This does not yet identify the image of LH with a binary parabolic
residual, or classify the restriction of B.5.1 to W. Those source steps
remain required before applying the C.4.8 row exclusions.

Source: Aschbacher--Smith C.2.9(2), printed p.147, and the final
parabolic calculation of C.4.8, printed p.154, in refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open ChapterC.Section04.BinaryThreeNaturalDualExclusion
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original intersection residual meets the radical in its entire two-core. -/
theorem binary_witness_core_eq_radical_intersection
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    LH.pCoreIn 2 = LH ⊓ J.pCoreIn 2 := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := hw.2.2.2.2.2.2.1
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy LH (H ⊓ normalizer (L : Set G)) = LH :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  have hj := hc.span_join_core
  have hl := hc.span_core_le_radical
  rw [hspan] at hj hl
  refine le_antisymm (le_inf (pCoreIn_le 2 LH) hl) ?_
  rw [←hj]
  exact inf_pCoreIn_le_of_le 2 le_sup_left

/-- The map into the literal quotient LH R/R has kernel O₂(LH). -/
theorem binary_witness_radicalQuotientMap_ker
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let R := J.pCoreIn 2
    let := normal_subgroupOf_sup_of_le_normalizer
      ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
        hw.2.2.2.2.2.2.1.span_normalizes_radical)
    (radicalQuotientMap LH R).ker = pCore 2 LH := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  let := normal_subgroupOf_sup_of_le_normalizer
    ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
      hw.2.2.2.2.2.2.1.span_normalizes_radical)
  have he : LH.pCoreIn 2 = LH ⊓ R := binary_witness_core_eq_radical_intersection hw
  ext l
  rw [MonoidHom.mem_ker]
  change QuotientGroup.mk' (R.subgroupOf (LH ⊔ R)) (inclusion le_sup_left l) = 1 ↔ _
  refine (QuotientGroup.eq_one_iff (inclusion le_sup_left l)).trans ?_
  change (l : G) ∈ R ↔ l ∈ pCore 2 LH
  constructor
  · intro hr
    have hp : (l : G) ∈ LH.pCoreIn 2 := he.symm ▸ ⟨l.property,hr⟩
    obtain ⟨x,hx,hxl⟩ := hp
    have hxl' : x = l := Subtype.ext hxl
    rwa [hxl'] at hx
  · intro hl
    have hp : (l : G) ∈ LH.pCoreIn 2 := mem_map_of_mem LH.subtype hl
    exact (he ▸ hp).2

/-- The actual radical quotient carries the original natural--dual marking,
including its compatibility with L and both conjugate seed axes. -/
theorem sourceOrbit_binary_witness_radical_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let R := J.pCoreIn 2
    let hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
    let := normal_subgroupOf_sup_of_le_normalizer
      ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
        hw.2.2.2.2.2.2.1.span_normalizes_radical)
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ q : L →* BinaryLinearThree.Group, Function.Surjective q ∧ q.ker = pCore 2 L ∧
      ∃ a : ((LH ⊔ R : Subgroup G) ⧸ R.subgroupOf (LH ⊔ R)) ≃* BinaryLinearThree.Group,
        (∀ l : LH, a (radicalQuotientMap LH R l) = q (inclusion hLH l)) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space,
        (∀ l v, E (doubledSeedAction LH D.sourceOrbit
          (hLH.trans D.sourceOrbit_component_normalizes) l v) =
            BinaryLinearThree.NaturalDual.action (a (radicalQuotientMap LH R l)) (E v)) ∧
        (∀ v, (E v).2 = 0 ↔ (v.toMul : G) ∈ V) ∧
        (∀ v, (E v).1 = 0 ↔ (v.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  have hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
  let := normal_subgroupOf_sup_of_le_normalizer
    ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
      hw.2.2.2.2.2.2.1.span_normalizes_radical)
  obtain ⟨t,ht,hnt,q,hq,hk,e,he,E,hE,hV,hVt⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let r := radicalQuotientMap LH R
  let b := QuotientGroup.quotientKerEquivOfSurjective r
    (radicalQuotientMap_surjective LH R)
  let c := QuotientGroup.quotientMulEquivOfEq (binary_witness_radicalQuotientMap_ker hw)
  let a := b.symm.trans (c.trans e)
  have ha (l : LH) : a (r l) = e (QuotientGroup.mk' (pCore 2 LH) l) := by
    change e (c (b.symm (r l))) = _
    have hb : b.symm (r l) = QuotientGroup.mk' r.ker l := by
      apply b.injective
      rw [b.apply_symm_apply]
      rfl
    rw [hb]
    rfl
  refine ⟨t,ht,hnt,q,hq,hk,a,fun l => (ha l).trans (he l),E,?_,hV,hVt⟩
  intro l v
  rw [ha]
  exact hE l v

/-- The full source orbit detects precisely the two-core of the original LH. -/
theorem sourceOrbit_binary_witness_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    (centralizer (D.sourceOrbit : Set G)).subgroupOf LH = pCore 2 LH := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
  obtain ⟨_,_,_,_,_,_,e,_,E,hE,_,_⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  ext l
  change (l : G) ∈ centralizer (D.sourceOrbit : Set G) ↔ l ∈ pCore 2 LH
  constructor
  · intro hl
    have hfix (v : Additive D.sourceOrbit) :
        doubledSeedAction LH D.sourceOrbit
          (hLH.trans D.sourceOrbit_component_normalizes) l v = v := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (l : G) * (v.toMul : G) * (l : G)⁻¹ = (v.toMul : G)
      exact mul_inv_eq_iff_eq_mul.mpr (hl v.toMul v.toMul.property).symm
    have ha : BinaryLinearThree.NaturalDual.action (e (QuotientGroup.mk' (pCore 2 LH) l)) = 1 := by
      apply LinearMap.ext
      intro w
      obtain ⟨v,rfl⟩ := E.surjective w
      change BinaryLinearThree.NaturalDual.action
        (e (QuotientGroup.mk' (pCore 2 LH) l)) (E v) = E v
      exact (hE l v).symm.trans (congrArg E (hfix v))
    have he : e (QuotientGroup.mk' (pCore 2 LH) l) = 1 :=
      BinaryLinearThree.NaturalDual.action_injective (by simpa only [map_one] using ha)
    exact (QuotientGroup.eq_one_iff l).mp (e.injective (he.trans e.map_one.symm))
  · intro hl w hwW
    let v : Additive D.sourceOrbit := Additive.ofMul ⟨w,hwW⟩
    have hlq : QuotientGroup.mk' (pCore 2 LH) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    have hfix : doubledSeedAction LH D.sourceOrbit
        (hLH.trans D.sourceOrbit_component_normalizes) l v = v := by
      apply E.injective
      rw [hE,hlq,map_one,map_one,Module.End.one_apply]
    have he := congrArg (fun z : Additive D.sourceOrbit => (z.toMul : G)) hfix
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

omit [Finite G] in
private theorem fixed_moved_core_centralizes (X Q : Subgroup G) :
    ⁅Q ⊓ centralizer (X.pCoreIn 2 : Set G),X⁆ ≤ centralizer (X.pCoreIn 2 : Set G) := by
  have hn : X ≤ normalizer (X.pCoreIn 2 : Set G) :=
    X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  exact (commutator_mono inf_le_right le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      (hn.trans (normalizer_le_normalizer_centralizer _)))

/-- The actual p.154 fixed-space commutator centralizes the original two-core,
and its full centralizer inside LH is exactly that core. -/
theorem sourceOrbit_binary_witness_fixed_moved_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let Q := (starV (K.map H.subtype) (J.pCoreIn 2)).map
      (K.map H.subtype ⊔ J.pCoreIn 2).subtype
    let W := ⁅Q ⊓ centralizer (LH.pCoreIn 2 : Set G),LH⁆
    W ≤ centralizer (LH.pCoreIn 2 : Set G) ∧
      (centralizer (W : Set G)).subgroupOf LH = pCore 2 LH := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Q := (starV (K.map H.subtype) (J.pCoreIn 2)).map
    (K.map H.subtype ⊔ J.pCoreIn 2).subtype
  let W := ⁅Q ⊓ centralizer (LH.pCoreIn 2 : Set G),LH⁆
  have hW := D.sourceOrbit_binary_witness_constrained_fixed_moved h hd F hF hmodel
    hw hWJ hJC K hK hq hout hfK
  have hc : W ≤ centralizer (LH.pCoreIn 2 : Set G) := fixed_moved_core_centralizes LH Q
  refine ⟨hc,le_antisymm ?_ ?_⟩
  · exact (subgroupOf_mono LH (centralizer_le hW.1)).trans_eq
      (D.sourceOrbit_binary_witness_centralizer h hd F hF hmodel hw)
  · intro l hl
    exact le_centralizer_iff.mp hc (mem_map_of_mem LH.subtype hl)

/-- The complete elementary fixed-space commutator has a faithful action of
the original quotient LH R/R, agreeing with ambient conjugation on every lift. -/
theorem sourceOrbit_binary_witness_fixed_moved_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let R := J.pCoreIn 2
    let Q := (starV (K.map H.subtype) R).map (K.map H.subtype ⊔ R).subtype
    let W := ⁅Q ⊓ centralizer (LH.pCoreIn 2 : Set G),LH⁆
    let := normal_subgroupOf_sup_of_le_normalizer
      ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
        hw.2.2.2.2.2.2.1.span_normalizes_radical)
    IsElementaryAbelian 2 W ∧
    ∃ ρ : ((LH ⊔ R : Subgroup G) ⧸ R.subgroupOf (LH ⊔ R)) →* MulAut W,
      Function.Injective ρ ∧
      ∀ (l : LH) (w : W), (ρ (radicalQuotientMap LH R l) w : G) =
        (l : G) * (w : G) * (l : G)⁻¹ := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  let Q := (starV (K.map H.subtype) R).map (K.map H.subtype ⊔ R).subtype
  let W := ⁅Q ⊓ centralizer (LH.pCoreIn 2 : Set G),LH⁆
  let := normal_subgroupOf_sup_of_le_normalizer
    ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
      hw.2.2.2.2.2.2.1.span_normalizes_radical)
  have hwN : LH ≤ normalizer (W : Set G) :=
    (D.sourceOrbit_binary_witness_constrained_fixed_moved h hd F hF hmodel
      hw hWJ hJC K hK hq hout hfK).2.2
  let f := W.normalizerMonoidHom.comp (inclusion hwN)
  have hker : f.ker = pCore 2 LH := by
    calc
      f.ker = (centralizer (W : Set G)).subgroupOf LH := by
        ext l
        change inclusion hwN l ∈ W.normalizerMonoidHom.ker ↔ _
        rw [normalizerMonoidHom_ker]
        rfl
      _ = _ := (D.sourceOrbit_binary_witness_fixed_moved_centralizer h hd F hF hmodel
        hw hWJ hJC K hK hq hout hfK).2
  let r := radicalQuotientMap LH R
  have hr : r.ker = pCore 2 LH := binary_witness_radicalQuotientMap_ker hw
  have hs : Function.Surjective r := radicalQuotientMap_surjective LH R
  let ρ := r.liftOfSurjective hs ⟨f,le_of_eq (hr.trans hker.symm)⟩
  have hρ (l : LH) : ρ (r l) = f l := by simp [ρ]
  have helem : IsElementaryAbelian 2 W := by
    let : IsElementaryAbelian 2 Q := IsElementaryAbelian.map_subtype
    have hWQ := (D.sourceOrbit_binary_witness_constrained_fixed_moved h hd F hF hmodel
      hw hWJ hJC K hK hq hout hfK).2.1
    exact IsElementaryAbelian.of_injective (inclusion hWQ) (inclusion_injective hWQ)
  refine ⟨helem,?_⟩
  refine ⟨ρ,(injective_iff_map_eq_one ρ).mpr ?_,?_⟩
  · intro x hx
    obtain ⟨l,rfl⟩ := hs x
    rw [hρ] at hx
    have hl : l ∈ r.ker := by
      rw [hr,←hker]
      exact hx
    exact hl
  · intro l w
    rw [hρ]
    rfl

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

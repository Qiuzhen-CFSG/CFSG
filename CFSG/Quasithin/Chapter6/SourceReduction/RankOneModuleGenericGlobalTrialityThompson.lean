module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtensionFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLongCentralizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtension.Recognition
public import Theory.GroupTheory.InvolutionClassOrderComparison
public import Theory.GroupTheory.CentralizerSmallKernelTransport
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCompletionFusionModel

/-!
# Thompson order comparison for the same constructed triality extension

Assume the designated short root has its native Sylow centralizer and that
its full ambient centralizer is identified, with the original left endpoint
map and pinned element retained, with the centralizer in the constructed
extension. These are exactly the outstanding short-root owner's inputs.
The already proved long-root centralizer isomorphism uses the other original
full-normalizer map in the same carrier.

The q^12 and q^10 source Sylow-centralizer orders then prevent the two pinned
extension roots from fusing: conjugate roots would have isomorphic full
centralizers and equal Sylow orders. The paired full-normalizer catalogue
therefore preserves and reflects both ambient involution classes. The marked
centralizer isomorphisms identify Thompson's two mixed-pair fibers. His order
formula proves equality of the full group and extension orders. The final
prepared recognizer consumes this equality on the very same constructed
carrier, retaining m=n>1 and an actual triality isomorphism.

This is a conditional assembly. The designated short-root extremality and
full marked centralizer must be discharged before claiming the original
prepared triality theorem or the generic global exit. Exhaustive selected-R
comparison and original source preparation remain separate obligations.
Source: Aschbacher--Smith F.4.40--44, printed pp.294--296, and 5.3.3--4,
printed p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates.Centers
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary TrialityCompletionFusion
variable {G : Type*} [Group G] [Finite G]

/-- The short-root extremality and full centralizer comparison prevent the
constructed extension from fusing the two pinned roots. The unequal Sylow
centralizer orders are q^12 and q^10, including q=4. -/
theorem Preparation.triality_extension_nonfusion_of_short_centralizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e)
    (hmodel : ∃ R : Sylow 2 (centralizer
        ({(shortElement (binaryParameters m hm) rfl).val} : Set (BinaryCarrier m hm))),
      (R : Subgroup _) = (unipotent (binaryParameters m hm)).subgroupOf
        (centralizer ({(shortElement (binaryParameters m hm) rfl).val} : Set (BinaryCarrier m hm))))
    (kt : centralizer ({(e.right.symm (shortElement (binaryParameters m hm) rfl)).val} : Set G) ≃*
      centralizer ({a.extension.baseHom (shortElement (binaryParameters m hm) rfl).val} :
        Set a.extension.carrier)) :
    ¬ IsConj (a.extension.baseHom (longElement (binaryParameters m hm) rfl).val)
      (a.extension.baseHom (shortElement (binaryParameters m hm) rfl).val) := by
  let P := binaryParameters m hm
  let z := (e.right.symm (longElement P rfl)).val
  let t := (e.right.symm (shortElement P rfl)).val
  let z' := a.extension.baseHom (longElement P rfl).val
  let t' := a.extension.baseHom (shortElement P rfl).val
  have hzU : (longElement P rfl).val ∈ unipotent P :=
    TrialityCompletionFusion.highest_U P rfl (by
      rw [←Triality.Standard.RadicalCoordinates.Centers.highestHom_range P rfl]
      exact ⟨_,rfl⟩)
  have htU : (shortElement P rfl).val ∈ unipotent P := TrialityCompletionFusion.short_U P rfl 2 1
  have hUC : unipotent P ≤ centralizer ({(longElement P rfl).val} : Set (BinaryCarrier m hm)) := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    obtain ⟨w,hw,he⟩ := highestRoot_le_center_unipotent P rfl
      (show (longElement P rfl).val ∈ highestRoot P from by
        rw [←Triality.Standard.RadicalCoordinates.Centers.highestHom_range P rfl]
        exact ⟨_,rfl⟩)
    rw [←he]
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨u,hu⟩)
  have hmodelZ : ∃ R : Sylow 2 (centralizer ({(longElement P rfl).val} : Set (BinaryCarrier m hm))),
      (R : Subgroup _) = (unipotent P).subgroupOf
        (centralizer ({(longElement P rfl).val} : Set (BinaryCarrier m hm))) :=
    ⟨(unipotentSylow P rfl).subtype hUC,rfl⟩
  obtain ⟨Rz,hRz⟩ := d.triality_involution_centralizer_sylow h hH hp m hm e
    (longElement P rfl) hzU (triality_pinned_root_orders m hm).1 hmodelZ
  obtain ⟨Rt,hRt⟩ := d.triality_involution_centralizer_sylow h hH hp m hm e
    (shortElement P rfl) htU (triality_pinned_root_orders m hm).2 hmodel
  have hcounts := d.triality_marked_sylow_centralizer_card h hH hp m hm e
  have hcz : Nat.card Rz = P.q^12 := by
    rw [hRz,←card_map_of_injective (centralizer ({z} : Set G)).subtype_injective,
      subgroupOf_map_subtype]
    exact hcounts.1
  have hct : Nat.card Rt = P.q^10 := by
    rw [hRt,←card_map_of_injective (centralizer ({t} : Set G)).subtype_injective,
      subgroupOf_map_subtype]
    exact hcounts.2
  obtain ⟨_,kz,_,_⟩ := d.triality_long_centralizer_full_marked h hH hp m hm e a
  intro hc
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  let kg := CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) z'
  have hcard : Nat.card (centralizer ({z} : Set G)) = Nat.card (centralizer ({t} : Set G)) := by
    calc
      _ = Nat.card (centralizer ({z'} : Set a.extension.carrier)) := Nat.card_congr kz.toEquiv
      _ = Nat.card (centralizer ({t'} : Set a.extension.carrier)) := by
        have hh := Nat.card_congr kg.toEquiv
        change Nat.card (centralizer ({z'} : Set a.extension.carrier)) =
          Nat.card (centralizer ({g*z'*g⁻¹} : Set a.extension.carrier)) at hh
        rwa [hg] at hh
      _ = _ := (Nat.card_congr kt.toEquiv).symm
  have hs : Nat.card Rz = Nat.card Rt := by
    rw [Rz.card_eq_multiplicity,Rt.card_eq_multiplicity,hcard]
  rw [hcz,hct] at hs
  exact (Nat.ne_of_lt (Nat.pow_lt_pow_right (by have := P.q_ge_two; omega : 1 < P.q)
    (by decide : 10 < 12))) hs.symm

/-- F.4.43 for the fixed triality extension, conditional only on the short-root
owner's model extremality and full marked ambient centralizer. Both Thompson
fibers, and hence the entire carrier order, are identified using the original
whole-normalizer maps. -/
theorem Preparation.triality_thompson_counts_of_short_centralizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e)
    (hmodel : ∃ R : Sylow 2 (centralizer
        ({(shortElement (binaryParameters m hm) rfl).val} : Set (BinaryCarrier m hm))),
      (R : Subgroup _) = (unipotent (binaryParameters m hm)).subgroupOf
        (centralizer ({(shortElement (binaryParameters m hm) rfl).val} : Set (BinaryCarrier m hm))))
    (hshort :
      let t := (e.right.symm (shortElement (binaryParameters m hm) rfl)).val
      let t' := a.extension.baseHom (shortElement (binaryParameters m hm) rfl).val
      ∃ ht : centralizer ({t} : Set G) ≤ normalizer (L : Set G),
        ∃ kt : centralizer ({t} : Set G) ≃* centralizer ({t'} : Set a.extension.carrier),
          (∀ x, (kt x).val = inclusion a.extension.right_le
            (a.comparison.left (inclusion ht x))) ∧
          kt ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ =
            ⟨t',mem_centralizer_singleton_iff.mpr rfl⟩) :
    let P := binaryParameters m hm
    let z := (e.right.symm (longElement P rfl)).val
    let t := (e.right.symm (shortElement P rfl)).val
    let z' := a.extension.baseHom (longElement P rfl).val
    let t' := a.extension.baseHom (shortElement P rfl).val
    TwoInvolutionClassOrder.kappa z t z = TwoInvolutionClassOrder.kappa z' t' z' ∧
      TwoInvolutionClassOrder.kappa z t t = TwoInvolutionClassOrder.kappa z' t' t' ∧
      Nat.card G = Nat.card a.extension.carrier := by
  let P := binaryParameters m hm
  let z := (e.right.symm (longElement P rfl)).val
  let t := (e.right.symm (shortElement P rfl)).val
  let z' := a.extension.baseHom (longElement P rfl).val
  let t' := a.extension.baseHom (shortElement P rfl).val
  obtain ⟨ht,kt,hkt,hpt⟩ := hshort
  obtain ⟨hz,kz,hkz,hpz⟩ := d.triality_long_centralizer_full_marked h hH hp m hm e a
  have hn := d.triality_comparison_involution_nonfusion h hH hp m hm e
  have hn' := d.triality_extension_nonfusion_of_short_centralizer h hH hp m hm e a hmodel kt
  obtain ⟨hleft,hright⟩ := d.triality_full_normalizer_fusion h hH hp m hm e a hn'
  have hroot := triality_pinned_root_orders m hm
  have hz2 : orderOf z = 2 := (Subgroup.orderOf_coe _).trans
    ((e.right.symm.orderOf_eq _).trans hroot.1)
  have ht2 : orderOf t = 2 := (Subgroup.orderOf_coe _).trans
    ((e.right.symm.orderOf_eq _).trans hroot.2)
  have hz2' : orderOf z' = 2 :=
    (orderOf_injective a.extension.baseHom (a.extension.baseHom_injective (conj_injective m hm)) _).trans
      ((Subgroup.orderOf_coe _).trans hroot.1)
  have ht2' : orderOf t' = 2 :=
    (orderOf_injective a.extension.baseHom (a.extension.baseHom_injective (conj_injective m hm)) _).trans
      ((Subgroup.orderOf_coe _).trans hroot.2)
  have hfz (x : centralizer ({z} : Set G)) :
      (IsConj z x.val ↔ IsConj z' (kz x).val) ∧
      (IsConj t x.val ↔ IsConj t' (kz x).val) := by
    rw [hkz]
    exact hright (inclusion hz x)
  have hft (x : centralizer ({t} : Set G)) :
      (IsConj z x.val ↔ IsConj z' (kt x).val) ∧
      (IsConj t x.val ↔ IsConj t' (kt x).val) := by
    rw [hkt]
    exact hleft (inclusion ht x)
  have hzpoint : InvolutionClassOrderComparison.centralizerPoint z =
      (⟨z,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({z} : Set G)) :=
    Subtype.ext (InvolutionClassOrderComparison.centralizerPoint_coe z)
  have htpoint : InvolutionClassOrderComparison.centralizerPoint t =
      (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set G)) :=
    Subtype.ext (InvolutionClassOrderComparison.centralizerPoint_coe t)
  have hzpoint' : InvolutionClassOrderComparison.centralizerPoint z' =
      (⟨z',mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({z'} : Set a.extension.carrier)) :=
    Subtype.ext (InvolutionClassOrderComparison.centralizerPoint_coe z')
  have htpoint' : InvolutionClassOrderComparison.centralizerPoint t' =
      (⟨t',mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t'} : Set a.extension.carrier)) :=
    Subtype.ext (InvolutionClassOrderComparison.centralizerPoint_coe t')
  have hpz' : kz (InvolutionClassOrderComparison.centralizerPoint z) =
      InvolutionClassOrderComparison.centralizerPoint z' :=
    (congrArg kz hzpoint).trans (hpz.trans hzpoint'.symm)
  have hpt' : kt (InvolutionClassOrderComparison.centralizerPoint t) =
      InvolutionClassOrderComparison.centralizerPoint t' :=
    (congrArg kt htpoint).trans (hpt.trans htpoint'.symm)
  have hkz' := InvolutionClassOrderComparison.kappa_eq z t z z' t' z'
    hz2 ht2 hn hz2' ht2' hn' kz hpz' (fun x => (hfz x).1) (fun x => (hfz x).2)
  have hkt' := InvolutionClassOrderComparison.kappa_eq z t t z' t' t'
    hz2 ht2 hn hz2' ht2' hn' kt hpt' (fun x => (hft x).1) (fun x => (hft x).2)
  refine ⟨hkz',hkt',?_⟩
  have hG := TwoInvolutionClassOrder.card_eq z t hz2 ht2 hn
    (fun x hx => d.triality_pinned_ambient_involution_classes h hH hp m hm e x hx)
  have hE := TwoInvolutionClassOrder.card_eq z' t' hz2' ht2' hn'
    (fun x hx => d.triality_extension_involution_classes h hH hp m hm e a x hx)
  rw [hkz',hkt',Nat.card_congr kz.toEquiv,Nat.card_congr kt.toEquiv] at hG
  exact hG.trans hE.symm

/-- Prepared triality recognition now needs only the designated short-root
centralizer results; the same constructed carrier's order is proved by Thompson
comparison, and the original exponent is retained. -/
theorem Preparation.triality_prepared_recognition_of_short_centralizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (hmodel : ∃ R : Sylow 2 (centralizer
        ({(shortElement (binaryParameters m hm) rfl).val} : Set (BinaryCarrier m hm))),
      (R : Subgroup _) = (unipotent (binaryParameters m hm)).subgroupOf
        (centralizer ({(shortElement (binaryParameters m hm) rfl).val} : Set (BinaryCarrier m hm))))
    (hshort :
      let a := d.trialityNormalizerMarking h hH hp m hm e
      let t := (e.right.symm (shortElement (binaryParameters m hm) rfl)).val
      let t' := a.extension.baseHom (shortElement (binaryParameters m hm) rfl).val
      ∃ ht : centralizer ({t} : Set G) ≤ normalizer (L : Set G),
        ∃ kt : centralizer ({t} : Set G) ≃* centralizer ({t'} : Set a.extension.carrier),
          (∀ x, (kt x).val = inclusion a.extension.right_le
            (a.comparison.left (inclusion ht x))) ∧
          kt ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ =
            ⟨t',mem_centralizer_singleton_iff.mpr rfl⟩) :
    let E := (d.trialityNormalizerMarking h hH hp m hm e).extension
    m = n ∧ 1 < m ∧
      normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      Nat.card G = Nat.card E.carrier ∧
      Nonempty (G ≃* BinaryCarrier m hm) ∧ ClassificationModels.IsRankTwoModel G n := by
  have hc := d.triality_thompson_counts_of_short_centralizer h hH hp m hm e
    (d.trialityNormalizerMarking h hH hp m hm e) hmodel hshort
  exact d.triality_prepared_extension_recognition_of_order h hH hp m hm e hc.2.2.le

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

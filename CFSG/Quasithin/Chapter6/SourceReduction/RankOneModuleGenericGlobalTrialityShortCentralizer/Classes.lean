module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Sylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtensionFusion
public import Theory.GroupTheory.CentralizerSmallKernelTransport
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCompletionFusionModel

/-!
# Class fidelity for the triality short-centralizer comparison

The native long and short centralizers have Sylow orders q^12 and q^10.
Thus a native automorphism cannot interchange the pinned roots, including
at q=4. This supplies the class-distinction premise of the published
whole-normalizer paired catalogue, used here for the F.4.42 incidence count.
No ambient order comparison or short-centralizer containment is assumed.

Source: Aschbacher--Smith F.4.27, F.4.35 and F.4.42, printed pp.288,292,295
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary TrialityCompletionFusion

private theorem automorphism_long_ne_short (m : ℕ) (hm : 0<m) (hm2 : 1<m)
    (a : MulAut (BinaryCarrier m hm)) :
    a (longElement (binaryParameters m hm) rfl).val ≠
      (shortElement (binaryParameters m hm) rfl).val := by
  let P := binaryParameters m hm
  let z := (longElement P rfl).val
  let t := (shortElement P rfl).val
  have hUC : unipotent P ≤ centralizer ({z} : Set (Carrier P)) := by
    intro u hu
    obtain ⟨w,hw,he⟩ := highestRoot_le_center_unipotent P rfl
      (show z ∈ highestRoot P from by
        rw [←highestHom_range P rfl]
        exact ⟨_,rfl⟩)
    apply mem_centralizer_singleton_iff.mpr
    rw [←he]
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨u,hu⟩)
  let Rz := (unipotentSylow P rfl).subtype hUC
  obtain ⟨Rt,hRt⟩ : ∃ Rt : Sylow 2 (centralizer ({t} : Set (Carrier P))),
      (Rt : Subgroup _) = (unipotent P).subgroupOf (centralizer ({t} : Set (Carrier P))) :=
    Triality.Standard.ShortRootCentralizer.centralizer_sylow m hm hm2 1 one_ne_zero
  have hcz : Nat.card Rz = P.q^12 := by
    change Nat.card ((unipotent P).subgroupOf (centralizer ({z} : Set (Carrier P)))) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv,card_unipotent_binary P rfl]
  have hct : Nat.card Rt = P.q^10 := by
    rw [hRt,←card_map_of_injective (centralizer ({t} : Set (Carrier P))).subtype_injective,
      subgroupOf_map_subtype]
    exact TrialityShortSylow.short_positive_centralizer_card m hm
  intro he
  have hc := Nat.card_congr
    (CentralizerSmallKernelTransport.centralizerEquiv a z).toEquiv
  change Nat.card (centralizer ({z} : Set (Carrier P))) =
    Nat.card (centralizer ({a z} : Set (Carrier P))) at hc
  rw [he] at hc
  have hs : Nat.card Rz = Nat.card Rt := by
    rw [Rz.card_eq_multiplicity,Rt.card_eq_multiplicity,hc]
  rw [hcz,hct] at hs
  exact (Nat.ne_of_lt (Nat.pow_lt_pow_right (by have := P.q_ge_two; omega) (by decide : 10<12))) hs.symm

variable {G : Type*} [Group G] [Finite G]
private theorem short_extension_classes_distinct
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e) :
    ¬ IsConj (a.extension.baseHom (longElement (binaryParameters m hm) rfl).val)
      (a.extension.baseHom (shortElement (binaryParameters m hm) rfl).val) := by
  intro hc
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  apply automorphism_long_ne_short m hm (d.triality_local_structure h hH.1.1.2 hp m hm e).2.1 g.val
  apply conj_injective m hm
  have he : MulAut.conj (g.val (longElement (binaryParameters m hm) rfl).val) =
      g.val * MulAut.conj (longElement (binaryParameters m hm) rfl).val * g.val⁻¹ := by
    ext y
    simp
  rw [he]
  exact congrArg Subtype.val hg

/-- The two literal normalizer maps preserve and reflect the classes needed
by the short-centralizer incidence comparison. -/
theorem Preparation.triality_short_centralizer_class_fidelity
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e) :
    let P := binaryParameters m hm
    (∀ x : normalizer (L : Set G),
      IsConj (e.right.symm (longElement P rfl)).val x.val ↔
        IsConj (a.extension.baseHom (longElement P rfl).val)
          (inclusion a.extension.right_le (a.comparison.left x))) ∧
    (∀ x : normalizer (residual H : Set G),
      IsConj (e.right.symm (shortElement P rfl)).val x.val ↔
        IsConj (a.extension.baseHom (shortElement P rfl).val)
          (inclusion a.extension.left_le (a.comparison.right x))) := by
  have hf := d.triality_full_normalizer_fusion h hH hp m hm e a
    (short_extension_classes_distinct d h hH hp m hm e a)
  exact ⟨fun x => (hf.1 x).1,fun x => (hf.2 x).2⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtensionOrder
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityExtension.Recognition

/-!
# The chosen-module triality extension: odd degree and marked centralizers

Each application uses the actual extension constructed from the supplied
pure comparison. The full source middle determines its exact outer degree,
which is odd because S=T. The native Sylow and involution representatives
therefore apply to that same carrier. The long ambient centralizer is
identified with its endpoint centralizer, preserving the original map.

The remaining short-root containment and ambient order comparison must still
be supplied to `rankOne_globalExit_of_triality_prepared_extension_order`.
These applications do not assert the final classification.

Source: Aschbacher--Smith F.4.38, F.4.40--43 and 5.3.3,
printed pp.294--296 and659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.SourceCompletion.TrialityNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original whole-middle index is the actual odd extension degree; the
native positive subgroup is Sylow in this same constructed carrier. -/
theorem rankOne_global_triality_extension_outer_data
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (nativeAmalgam m hm).reverse) :
    let a := d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp m hm e
    let C := ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1
    let N := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
    a.extension.nativeOverlap.index = C.relIndex N ∧
      ¬ 2 ∣ a.extension.nativeOverlap.index ∧
      Nat.card a.extension.carrier = Nat.card (BinaryCarrier m hm) * C.relIndex N ∧
      ∃ Q : Sylow 2 a.extension.carrier,
        (Q : Subgroup _) = (unipotent (binaryParameters m hm)).map a.extension.baseHom := by
  let h₀ := D.rankOne_generic_input_of_many h hmany hn hpsl
  let a := d.trialityNormalizerMarking h₀ hH hp m hm e
  exact ⟨a.outer_index_eq_source,d.triality_extension_outer_odd h₀ hH hp m hm e a,
    a.card_eq_source,d.triality_extension_native_sylow h₀ hH hp m hm e a⟩

/-- Every involution of the constructed carrier belongs to its native inner group. -/
theorem rankOne_global_triality_extension_involution_lift
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (nativeAmalgam m hm).reverse)
    (x : (d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp m hm e).extension.carrier) (hx : orderOf x = 2) :
    ∃ v : BinaryCarrier m hm, orderOf v = 2 ∧
      (d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp m hm e).extension.baseHom v = x :=
  d.triality_extension_involution_lift (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm e _ x hx

/-- The original marking's two pinned native roots cover all extension involutions. -/
theorem rankOne_global_triality_extension_involution_classes
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (nativeAmalgam m hm).reverse) :
    let a := d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp m hm e
    let P := binaryParameters m hm
    ∀ x : a.extension.carrier, orderOf x = 2 →
      IsConj (a.extension.baseHom (Global.TrialityCompletionFusion.longElement P rfl).val) x ∨
      IsConj (a.extension.baseHom (Global.TrialityCompletionFusion.shortElement P rfl).val) x :=
  fun x hx => d.triality_extension_involution_classes
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e _ x hx

/-- The literal ambient long centralizer is transported through the original
full normalizer to the endpoint centralizer inside the constructed carrier. -/
theorem rankOne_global_triality_long_centralizer_marked
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (nativeAmalgam m hm).reverse) :
    let a := d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp m hm e
    let P := binaryParameters m hm
    let z := (e.right.symm (Global.TrialityCompletionFusion.longElement P rfl)).val
    ∃ hz : centralizer ({z} : Set G) ≤ normalizer (residual H : Set G),
      ∃ k : centralizer ({z} : Set G) ≃*
        (a.extension.left.subgroupOf a.extension.carrier ⊓ centralizer
          ({a.extension.baseHom (Global.TrialityCompletionFusion.longElement P rfl).val} :
            Set a.extension.carrier) : Subgroup _),
        ∀ x, (k x).val = inclusion a.extension.left_le
          (a.comparison.right (inclusion hz x)) :=
  d.triality_long_centralizer_marked (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm e _

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

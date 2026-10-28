module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.NativeLift
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionTriality

/-!
# Lifting compatible original triality conjugation maps

Transport a compatible automorphism of the original parabolic amalgam through
its actual reversed triality comparison. The native marked lifting theorem
extends both local maps simultaneously. If those maps are original conjugation
by g, the resulting native automorphism has precisely those transported values.
No ambient extension or order bound occurs in this application. Constructing
source compatibility and normalizing the original pair remain with the source
owner; neither is replaced by a native recognition assumption.

Source: Aschbacher--Smith 5.3.2, p.659, using F.4.24, pp.287--288.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary
open _root_.Triality.Standard
variable {G : Type*} [Group G] [Finite G]

/-- Both compatible source conjugation maps extend on the actual native carrier,
with the central/arms reversal and the original exponent retained. -/
theorem Preparation.triality_native_conjugation_lift
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (nativeAmalgam m hm).reverse)
    (a : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (sourceParabolicAmalgam ![L,R] (sourceS L H)))
    (g : G)
    (hl : ∀ x, (a.left x).val=g*x.val*g⁻¹)
    (hr : ∀ x, (a.right x).val=g*x.val*g⁻¹) :
    m=n ∧ 1<m ∧ ∃ f : MulAut (BinaryCarrier m hm),
      (∀ x, f (e.left x).val =
        (e.left ⟨g*x.val*g⁻¹,by rw [←hl x]; exact (a.left x).property⟩).val) ∧
      (∀ x, f (e.right x).val =
        (e.right ⟨g*x.val*g⁻¹,by rw [←hr x]; exact (a.right x).property⟩).val) := by
  obtain ⟨hmn,hm2,_⟩ := d.triality_local_structure h hTH hp m hm e
  let b := RankTwoAmalgam.automorphismConjEquiv e a
  obtain ⟨f,hfl,hfr⟩ := native_amalgam_automorphism hm2 b.reverse
  refine ⟨hmn,hm2,f,?_,?_⟩
  · intro x
    have hh := hfr (e.left x)
    change f (e.left x).val=(e.left (a.left (e.left.symm (e.left x)))).val at hh
    rw [e.left.symm_apply_apply] at hh
    exact hh.trans (congrArg (fun y => (e.left y).val) (Subtype.ext (hl x)))
  · intro x
    have hh := hfl (e.right x)
    change f (e.right x).val=(e.right (a.right (e.right.symm (e.right x)))).val at hh
    rw [e.right.symm_apply_apply] at hh
    exact hh.trans (congrArg (fun y => (e.right y).val) (Subtype.ext (hr x)))
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

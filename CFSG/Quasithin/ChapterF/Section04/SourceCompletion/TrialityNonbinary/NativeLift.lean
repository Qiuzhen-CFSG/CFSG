module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.Recognition
public import Theory.GroupTheory.Amalgam.AutomorphismTransport

/-!
# Native triality automorphisms from both marked local actions

Pure inner conjugation identifies the actual native amalgam with an extension
amalgam. Twisting its model marking changes neither carrier nor order. Marked
recognition therefore extends both compatible endpoint automorphisms to one
native automorphism. The order bound is reflexivity on this concrete carrier;
no ambient source order bound or recognition is used.

Source: Aschbacher--Smith 5.3.2 and F.4.24, pp.659,287--288.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
open Subgroup Theory.GroupTheory
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

/-- The algebraic pure-inner extension of any pair of subgroups. -/
def innerExtension {K : Type*} [Group K] (P Q : Subgroup K) :
    UnitaryNonbinary.SourceExtension P Q where
  carrier := UnitaryNonbinary.inner K
  left := P.map MulAut.conj
  right := Q.map MulAut.conj
  left_le := Subgroup.map_le_range _ _
  right_le := Subgroup.map_le_range _ _
  contains_inner := le_rfl
  preserves_types := by
    rintro _ ⟨g,rfl⟩
    exact ⟨⟨g,rfl⟩,⟨g,rfl⟩⟩
  left_inner := inf_eq_left.mpr (Subgroup.map_le_range _ _)
  right_inner := inf_eq_left.mpr (Subgroup.map_le_range _ _)
  factor := by
    rintro _ ⟨g,rfl⟩
    exact ⟨g,1,one_mem _,(mul_one _).symm⟩

/-- Faithful inner conjugation identifies the complete intersection amalgam. -/
def innerComparison {K : Type*} [Group K] (P Q : Subgroup K)
    (hi : Function.Injective (MulAut.conj : K →* MulAut K)) :
    RankTwoAmalgam.Iso
      (UnitaryNonbinary.SourceExtension.nativeAmalgam (P₀ := P) (P₁ := Q))
      (innerExtension P Q).amalgam where
  left := P.equivMapOfInjective MulAut.conj hi
  middle := ((P ⊓ Q).equivMapOfInjective MulAut.conj hi).trans
    (MulEquiv.subgroupCongr (Subgroup.map_inf P Q MulAut.conj hi))
  right := Q.equivMapOfInjective MulAut.conj hi
  left_commutes _ := by apply Subtype.ext; rfl
  right_commutes _ := by apply Subtype.ext; rfl

/-- The pure-inner extension, with its literal native endpoint images. -/
def pureInner (m : ℕ) (hm : 0 < m) : SourceExtension m hm :=
  innerExtension (parabolic (binaryParameters m hm) .arms)
    (parabolic (binaryParameters m hm) .central)

/-- Faithful conjugation transports the entire native Borel and both endpoints. -/
def pureComparison (m : ℕ) (hm : 0 < m) :
    RankTwoAmalgam.Iso (nativeAmalgam m hm) (pureInner m hm).amalgam :=
  (nativeIntersectionIso m hm).trans
    (innerComparison (parabolic (binaryParameters m hm) .arms)
      (parabolic (binaryParameters m hm) .central) (conj_injective m hm))

/-- The native group is the actual pure-inner extension carrier. -/
def pureCarrierEquiv (m : ℕ) (hm : 0 < m) : BinaryCarrier m hm ≃* (pureInner m hm).carrier :=
  MonoidHom.ofInjective (conj_injective m hm)

/-- Every compatible extension-diagram automorphism extends with both markings. -/
theorem extension_amalgam_automorphism {m : ℕ} {hm : 0 < m} (hm2 : 1 < m)
    (E : SourceExtension m hm) (a : RankTwoAmalgam.Iso E.amalgam E.amalgam) :
    ∃ f : MulAut E.carrier,
      (∀ x, f ((modelCompletion E).left x) = (modelCompletion E).left (a.left x)) ∧
      (∀ x, f ((modelCompletion E).right x) = (modelCompletion E).right (a.right x)) := by
  let d := (modelCompletion E).comapIso a
  have ho : d.left.range ⊓ d.right.range=d.middle.range := by
    simpa only [d,RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using modelCompletion_overlap E
  obtain ⟨f,hl,hr⟩ := exists_marked_mulEquiv_of_card_le E d hm2 ho le_rfl
  refine ⟨f.symm,?_,?_⟩
  · intro x
    rw [←hl x,f.symm_apply_apply]
    rfl
  · intro x
    rw [←hr x,f.symm_apply_apply]
    rfl

/-- A native automorphism extends both given local actions on their entire
parabolics, retaining the common Borel and the two unequal type labels. -/
theorem native_amalgam_automorphism {m : ℕ} {hm : 0 < m} (hm2 : 1 < m)
    (a : RankTwoAmalgam.Iso (nativeAmalgam m hm) (nativeAmalgam m hm)) :
    ∃ f : MulAut (BinaryCarrier m hm),
      (∀ x : parabolic (binaryParameters m hm) .arms, f x.val=(a.left x).val) ∧
      (∀ x : parabolic (binaryParameters m hm) .central, f x.val=(a.right x).val) := by
  let e := pureComparison m hm
  let b := RankTwoAmalgam.automorphismConjEquiv e a
  obtain ⟨f,hl,hr⟩ := extension_amalgam_automorphism hm2 (pureInner m hm) b
  let z := pureCarrierEquiv m hm
  refine ⟨z.trans (f.trans z.symm),?_,?_⟩
  · intro x
    apply z.injective
    change z (z.symm (f (z x.val)))=z (a.left x).val
    rw [z.apply_symm_apply]
    change f ((modelCompletion (pureInner m hm)).left (e.left x))=
      (modelCompletion (pureInner m hm)).left (e.left (a.left x))
    rw [hl]
    congr 1
    change e.left (a.left (e.left.symm (e.left x)))=_
    rw [e.left.symm_apply_apply]
  · intro x
    apply z.injective
    change z (z.symm (f (z x.val)))=z (a.right x).val
    rw [z.apply_symm_apply]
    change f ((modelCompletion (pureInner m hm)).right (e.right x))=
      (modelCompletion (pureInner m hm)).right (e.right (a.right x))
    rw [hr]
    congr 1
    change e.right (a.right (e.right.symm (e.right x)))=_
    rw [e.right.symm_apply_apply]
end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary

module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.Geometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Inner
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.Triality

/-!
# The literal native subgroup of a full triality completion

The native arms and central endpoint images generate a normal subgroup,
supplemented by the full extension overlap. Restricting the given marking
gives a faithful completion of the native amalgam in that subgroup, with
exactly its native Borel overlap. No identification of that subgroup with
the triality carrier is assumed here.

Source: Aschbacher--Smith F.4.3--6 and F.4.17, pp.274--277,283.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
open Subgroup Theory.GroupTheory
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

abbrev nativeAmalgam (m : ℕ) (hm : 0 < m) :=
  GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)

abbrev NativeCompletion (m : ℕ) (hm : 0 < m) (M : Type*) [Group M] :=
  RankTwoAmalgam.FaithfulCompletion (nativeAmalgam m hm) (G := M)

/-- The known native carrier with its two inclusion markings. -/
def nativeModel (m : ℕ) (hm : 0 < m) : NativeCompletion m hm (BinaryCarrier m hm) :=
  .ofSubgroups (parabolic (binaryParameters m hm) .arms) (borel (binaryParameters m hm))
    (parabolic (binaryParameters m hm) .central)
    (borel_le_parabolic _ _) (borel_le_parabolic _ _) (native_generate m hm)

theorem nativeModel_family (m : ℕ) (hm : 0 < m) :
    (nativeModel m hm).cosetFamily = SmallCompletion.family m hm := by
  funext i
  cases i <;> exact range_subtype _

theorem nativeModel_overlap (m : ℕ) (hm : 0 < m) :
    (nativeModel m hm).left.range ⊓ (nativeModel m hm).right.range =
      (nativeModel m hm).middle.range := by
  change (parabolic (binaryParameters m hm) .arms).subtype.range ⊓
    (parabolic (binaryParameters m hm) .central).subtype.range = _
  rw [range_subtype, range_subtype]
  exact (parabolic_inf_binary _ rfl).trans
    (RankTwoAmalgam.FaithfulCompletion.ofSubgroups_middle_range _ _ _ _ _ _).symm

variable {m : ℕ} {hm : 0 < m} (E : SourceExtension m hm)
variable {M : Type*} [Group M] (c : Completion E M)

/-- The join of the literal native endpoint images in the supplied completion. -/
abbrev nativeCore : Subgroup M := E.innerGenerated c

theorem nativeCore_normal : (nativeCore E c).Normal :=
  E.innerGenerated_normal c (conj_injective m hm)

theorem nativeCore_sup_middle : nativeCore E c ⊔ c.middle.range = ⊤ :=
  E.innerGenerated_sup_middle c (conj_injective m hm)

/-- The native Borel is exactly the intersection, with identity endpoint maps. -/
def nativeIntersectionIso (m : ℕ) (hm : 0 < m) :
    RankTwoAmalgam.Iso (nativeAmalgam m hm)
      (UnitaryNonbinary.SourceExtension.nativeAmalgam
        (P₀ := parabolic (binaryParameters m hm) .arms)
        (P₁ := parabolic (binaryParameters m hm) .central)) where
  left := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr (parabolic_inf_binary _ rfl).symm
  right := MulEquiv.refl _
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

/-- Restriction to the genuine native arms/Borel/central amalgam. -/
def nativeCompletion : NativeCompletion m hm (nativeCore E c) :=
  (E.innerCompletion c (conj_injective m hm)).comapIso (nativeIntersectionIso m hm)

/-- Whole extension overlap restricts to precisely the native Borel image. -/
theorem nativeCompletion_overlap
    (ho : c.left.range ⊓ c.right.range = c.middle.range) :
    (nativeCompletion E c).left.range ⊓ (nativeCompletion E c).right.range =
      (nativeCompletion E c).middle.range := by
  unfold nativeCompletion
  rw [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
    RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
    RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range]
  exact E.innerCompletion_overlap c (conj_injective m hm) ho

@[simp] theorem nativeCompletion_left_val (x : parabolic (binaryParameters m hm) .arms) :
    ((nativeCompletion E c).left x).val = c.left (E.nativeLeft x) := rfl

@[simp] theorem nativeCompletion_right_val (x : parabolic (binaryParameters m hm) .central) :
    ((nativeCompletion E c).right x).val = c.right (E.nativeRight x) := rfl

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary

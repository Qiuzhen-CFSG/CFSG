module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.NativeRestoration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ExtensionDiagram
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.NativeLift
public import Theory.SpecificGroups.Triality.ParabolicNormalizer

/-!
# Original triality restoration in both orientations

The native lift of every reduced triality amalgam automorphism preserves the
actual universal kernel. The reduced parabolics are self-normalizing and have
exact Borel intersection, so descent constructs compatible maps of both original
endpoints into a type-preserving automorphism extension of the genuine carrier.
The entire original Borel and both reduced endpoint restrictions are retained.
The original Borel index divides the cubic field period. At odd degree every
two-power actor is inner and the original Sylow equals the reduced Sylow; at
even degree the actual extension is retained.

Source: DGS, *Groups and Graphs* (1985), (15.2), printed pp.226–228.
The marked nonbinary reduced comparison remains an explicit recognition input.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.TrialityNative
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open SourceCompletion

def side (i : Bool) : Node := if i then .central else .arms

def amalgam (m : ℕ) (hm : 0 < m) (i : Bool) : RankTwoAmalgam
    (Parabolics.parabolic (binaryParameters m hm) (side i)) (Parabolics.borel (binaryParameters m hm))
    (Parabolics.parabolic (binaryParameters m hm) (side (!i))) :=
  ofSubgroups _ _ _ (borel_le_parabolic _ _) (borel_le_parabolic _ _)

def model (m : ℕ) (hm : 0 < m) (i : Bool) :
    FaithfulCompletion (amalgam m hm i) (G := BinaryCarrier m hm) :=
  .ofSubgroups _ _ _ (borel_le_parabolic _ _) (borel_le_parabolic _ _) (by
    cases i
    · exact parabolic_sup_binary _ rfl
    · change Parabolics.parabolic (binaryParameters m hm) .central ⊔
        Parabolics.parabolic (binaryParameters m hm) .arms = ⊤
      rw [sup_comm]
      exact parabolic_sup_binary _ rfl)

theorem model_left_range (m : ℕ) (hm : 0 < m) (i : Bool) :
    (model m hm i).left.range = Parabolics.parabolic (binaryParameters m hm) (side i) :=
  FaithfulCompletion.ofSubgroups_left_range ..
theorem model_right_range (m : ℕ) (hm : 0 < m) (i : Bool) :
    (model m hm i).right.range = Parabolics.parabolic (binaryParameters m hm) (side (!i)) :=
  FaithfulCompletion.ofSubgroups_right_range ..
theorem model_middle_range (m : ℕ) (hm : 0 < m) (i : Bool) :
    (model m hm i).middle.range = Parabolics.borel (binaryParameters m hm) :=
  FaithfulCompletion.ofSubgroups_middle_range ..

theorem model_overlap (m : ℕ) (hm : 0 < m) (i : Bool) :
    (model m hm i).left.range ⊓ (model m hm i).right.range =
      (model m hm i).middle.range := by
  rw [model_left_range, model_right_range, model_middle_range]
  cases i
  · exact parabolic_inf_binary _ rfl
  · exact (inf_comm _ _).trans (parabolic_inf_binary _ rfl)

theorem native_lifts {m : ℕ} {hm : 0 < m} (hm2 : 1 < m) (i : Bool)
    (a : Iso (amalgam m hm i) (amalgam m hm i)) :
    ∃ f : BinaryCarrier m hm →* BinaryCarrier m hm,
      (∀ x, f ((model m hm i).left x) = (model m hm i).left (a.left x)) ∧
      (∀ x, f ((model m hm i).right x) = (model m hm i).right (a.right x)) := by
  cases i
  · obtain ⟨f,hl,hr⟩ := TrialityNonbinary.native_amalgam_automorphism hm2 a
    exact ⟨f.toMonoidHom,hl,hr⟩
  · obtain ⟨f,hl,hr⟩ := TrialityNonbinary.native_amalgam_automorphism hm2 a.reverse
    exact ⟨f.toMonoidHom,hr,hl⟩

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) (m : ℕ) (hm : 0 < m) (i : Bool)
  (e : Iso (reducedAmalgam L S) (amalgam m hm i))

abbrev reducedCompletion := (model m hm i).comapIso e

theorem reduced_preserved (hm2 : 1 < m) :
    PreservesCompletionKernel h (reducedCompletion m hm i e) :=
  NativeRestoration.preserves_of_native_lifts (reducedOverlapAction h) e (model m hm i)
    (native_lifts hm2 i)

theorem reduced_overlap :
    (reducedCompletion m hm i e).left.range ⊓ (reducedCompletion m hm i e).right.range =
      (reducedCompletion m hm i e).middle.range := by
  simp only [reducedCompletion, FaithfulCompletion.comapIso_left_range,
    FaithfulCompletion.comapIso_right_range, FaithfulCompletion.comapIso_middle_range]
  exact model_overlap m hm i

theorem reduced_normalizer (j : Fin 2) :
    normalizer ((completionEndpoint (reducedCompletion m hm i e) j).range :
      Set (BinaryCarrier m hm)) = (completionEndpoint (reducedCompletion m hm i e) j).range := by
  fin_cases j
  · change normalizer ((reducedCompletion m hm i e).left.range : Set (BinaryCarrier m hm)) =
      (reducedCompletion m hm i e).left.range
    rw [FaithfulCompletion.comapIso_left_range,model_left_range]
    exact normalizer_parabolic_binary _ rfl _
  · change normalizer ((reducedCompletion m hm i e).right.range : Set (BinaryCarrier m hm)) =
      (reducedCompletion m hm i e).right.range
    rw [FaithfulCompletion.comapIso_right_range,model_right_range]
    exact normalizer_parabolic_binary _ rfl _

/-- The entire original overlap and both parabolics form an actual regular
extension of the genuine triality carrier. Even outer degree is retained. -/
def extension (hm2 : 1 < m) : UnitaryNonbinary.SourceExtension
    (Parabolics.parabolic (binaryParameters m hm) (side i))
    (Parabolics.parabolic (binaryParameters m hm) (side (!i))) where
  carrier := (restoredSourceExtension h (reducedCompletion m hm i e) (reduced_preserved h m hm i e hm2)
    (reduced_overlap m hm i e) (reduced_normalizer m hm i e)).carrier
  left := (restoredSourceExtension h (reducedCompletion m hm i e) (reduced_preserved h m hm i e hm2)
    (reduced_overlap m hm i e) (reduced_normalizer m hm i e)).left
  right := (restoredSourceExtension h (reducedCompletion m hm i e) (reduced_preserved h m hm i e hm2)
    (reduced_overlap m hm i e) (reduced_normalizer m hm i e)).right
  left_le := (restoredSourceExtension h (reducedCompletion m hm i e) (reduced_preserved h m hm i e hm2)
    (reduced_overlap m hm i e) (reduced_normalizer m hm i e)).left_le
  right_le := (restoredSourceExtension h (reducedCompletion m hm i e) (reduced_preserved h m hm i e hm2)
    (reduced_overlap m hm i e) (reduced_normalizer m hm i e)).right_le
  contains_inner := (restoredSourceExtension h (reducedCompletion m hm i e) (reduced_preserved h m hm i e hm2)
    (reduced_overlap m hm i e) (reduced_normalizer m hm i e)).contains_inner
  preserves_types := by
    intro a ha
    have hh := (restoredSourceExtension h (reducedCompletion m hm i e) (reduced_preserved h m hm i e hm2)
    (reduced_overlap m hm i e) (reduced_normalizer m hm i e)).preserves_types a ha
    simpa only [reducedCompletion,FaithfulCompletion.comapIso_left_range,
      FaithfulCompletion.comapIso_right_range,model_left_range,model_right_range] using hh
  left_inner := by
    have hh := (restoredSourceExtension h (reducedCompletion m hm i e) (reduced_preserved h m hm i e hm2)
    (reduced_overlap m hm i e) (reduced_normalizer m hm i e)).left_inner
    simpa only [reducedCompletion,FaithfulCompletion.comapIso_left_range,model_left_range] using hh
  right_inner := by
    have hh := (restoredSourceExtension h (reducedCompletion m hm i e) (reduced_preserved h m hm i e hm2)
    (reduced_overlap m hm i e) (reduced_normalizer m hm i e)).right_inner
    simpa only [reducedCompletion,FaithfulCompletion.comapIso_right_range,model_right_range] using hh
  factor := (restoredSourceExtension h (reducedCompletion m hm i e) (reduced_preserved h m hm i e hm2)
    (reduced_overlap m hm i e) (reduced_normalizer m hm i e)).factor

/-- Exact original marking, including every element of the whole original
Borel and both reduced endpoint restrictions, into the same extension. -/
theorem exists_original_extension_iso (hm2 : 1 < m) :
    ∃ f : Iso (originalAmalgam L S) (extension h m hm i e hm2).amalgam,
      (∀ b : commonBorel L S, (f.middle b : MulAut (BinaryCarrier m hm)) =
        completionAction h (reducedCompletion m hm i e) (reduced_preserved h m hm i e hm2) b) ∧
      (∀ x : Source.parabolic L (SuzukiContainment.reducedSylow L S) 0,
        (f.left (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x) :
          MulAut (BinaryCarrier m hm)) = MulAut.conj ((e.left x : Parabolics.parabolic _ _) : BinaryCarrier m hm)) ∧
      (∀ x : Source.parabolic L (SuzukiContainment.reducedSylow L S) 1,
        (f.right (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x) :
          MulAut (BinaryCarrier m hm)) = MulAut.conj ((e.right x : Parabolics.parabolic _ _) : BinaryCarrier m hm)) :=
  exists_original_sourceExtension_iso h (reducedCompletion m hm i e)
    (reduced_preserved h m hm i e hm2) (reduced_overlap m hm i e) (reduced_normalizer m hm i e)

include h e in
/-- The permissible outer index is the original Borel index and divides
its actual cubic coefficient period; no two-power index bound is guessed. -/
theorem original_borel_index_dvd (hm2 : 1 < m) :
    (commonBorel L (SuzukiContainment.reducedSylow L S)).relIndex (commonBorel L S) ∣ 3*m := by
  rw [← original_outer_index h (reducedCompletion m hm i e)
    (reduced_preserved h m hm i e hm2) (reduced_overlap m hm i e) (reduced_normalizer m hm i e)]
  exact ((MulAut.innerSubgroup (BinaryCarrier m hm)).relIndex_dvd_index_of_normal _).trans
    (ParabolicOuterTwo.outer_card_dvd m hm)

/-- For odd field degree every two-power actor is inner; the cubic coefficient
period is retained when proving coprimality. -/
theorem twoPower_inner_of_odd (hmOdd : Odd m) (a : MulAut (BinaryCarrier m hm))
    (k : ℕ) (ha : a^(2^k) = 1) : a ∈ MulAut.innerSubgroup (BinaryCarrier m hm) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier m hm))
  have hp : q a ^ (2^k) = 1 := by rw [← map_pow,ha,map_one]
  have hd : orderOf (q a) ∣ 3*m :=
    (_root_.orderOf_dvd_natCard _).trans (ParabolicOuterTwo.outer_card_dvd m hm)
  have hc : Nat.Coprime (2^k) (3*m) :=
    ((by decide : Nat.Coprime 2 3).mul_right (Nat.coprime_two_left.mpr hmOdd)).pow_left k
  exact (QuotientGroup.eq_one_iff a).mp (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one hp) hd))

include h e in
/-- Odd field degree forces the original Sylow to equal the reduced one. -/
theorem original_sylow_eq_reduced (hm2 : 1 < m) (hmOdd : Odd m) :
    S = SuzukiContainment.reducedSylow L S :=
  NativeRestoration.sylow_eq_reduced_of_twoPower_inner h (reducedCompletion m hm i e)
    (reduced_preserved h m hm i e hm2) (reduced_overlap m hm i e) (reduced_normalizer m hm i e)
    (twoPower_inner_of_odd m hm hmOdd)

/-- The native comparison follows at odd degree, with no extension-collapse
premise. At even degree the actual regular extension above is retained. -/
def originalIso (hm2 : 1 < m) (hmOdd : Odd m) : Iso (originalAmalgam L S) (amalgam m hm i) :=
  (NativeRestoration.originalIsoReduced (original_sylow_eq_reduced h m hm i e hm2 hmOdd)).trans e

theorem originalIso_reduced (hm2 : 1 < m) (hmOdd : Odd m) :
    (∀ x : Source.parabolic L (SuzukiContainment.reducedSylow L S) 0,
      (originalIso h m hm i e hm2 hmOdd).left
        (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x) = e.left x) ∧
    (∀ x : commonBorel L (SuzukiContainment.reducedSylow L S),
      (originalIso h m hm i e hm2 hmOdd).middle
        (inclusion (SuzukiContainment.reduced_commonBorel_le h) x) = e.middle x) ∧
    (∀ x : Source.parabolic L (SuzukiContainment.reducedSylow L S) 1,
      (originalIso h m hm i e hm2 hmOdd).right
        (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x) = e.right x) :=
  NativeRestoration.originalIsoReduced_trans_reduced h
    (original_sylow_eq_reduced h m hm i e hm2 hmOdd) e

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.TrialityNative

module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.NativeRestoration
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.AmalgamActions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.SuzukiContainment

/-!
# Original restoration for the nonbinary Ree row

The native Ree amalgam lift extends every compatible automorphism in both
orientations. It therefore preserves the actual universal completion kernel
of any genuinely marked reduced comparison. Sylow conjugacy proves that
both concrete endpoint images are self-normalizing. The full original Borel
thus acts faithfully on the native completion.

Every two-power automorphism of this Ree model is inner. Applied to the
original source S, the marked inner-preimage calculation forces S to equal
its reduced subgroup. The resulting isomorphism restores both original
endpoints and the whole original Borel, with the exact reduced restrictions.
The final application gives containment of the same original ambient Sylow
T in the selected right factor R.

Source: DGS, *Groups and Graphs* (1985), (15.2), pp.226–228, and
Aschbacher–Smith F.1.12, pp.263–264. A genuine marked reduced isomorphism
remains an input. All parameters m>0 and both orientations are retained;
the binary TYPE alternatives do not supply such an isomorphism.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.ReeNative
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open SourceCompletion.GeneralReeFour

def side (i : Bool) : Side := if i then .suzuki else .linear

def amalgam (m : ℕ) (i : Bool) : RankTwoAmalgam
    (ReeF4.Parabolics.parabolic m (side i)) (ReeF4.Parabolics.borel m)
    (ReeF4.Parabolics.parabolic m (side (!i))) :=
  ofSubgroups _ _ _ (borel_le_parabolic m (side i)) (borel_le_parabolic m (side (!i)))

def model (m : ℕ) (i : Bool) : FaithfulCompletion (amalgam m i) (G := Model m) :=
  FaithfulCompletion.ofSubgroups _ _ _ (borel_le_parabolic m (side i))
    (borel_le_parabolic m (side (!i))) (by
      cases i
      · change ReeF4.Parabolics.parabolic m .linear ⊔ ReeF4.Parabolics.parabolic m .suzuki = ⊤
        rw [sup_comm]
        exact GreenBook.LieModels.ReeFour.parabolics_generate m
      · exact GreenBook.LieModels.ReeFour.parabolics_generate m)

theorem model_left_range (m : ℕ) (i : Bool) :
    (model m i).left.range = ReeF4.Parabolics.parabolic m (side i) :=
  FaithfulCompletion.ofSubgroups_left_range ..
theorem model_right_range (m : ℕ) (i : Bool) :
    (model m i).right.range = ReeF4.Parabolics.parabolic m (side (!i)) :=
  FaithfulCompletion.ofSubgroups_right_range ..
theorem model_middle_range (m : ℕ) (i : Bool) :
    (model m i).middle.range = ReeF4.Parabolics.borel m :=
  FaithfulCompletion.ofSubgroups_middle_range ..

theorem model_overlap (m : ℕ) (i : Bool) :
    (model m i).left.range ⊓ (model m i).right.range = (model m i).middle.range := by
  rw [model_left_range,model_right_range,model_middle_range]
  cases i
  · exact (inf_comm _ _).trans (GreenBook.LieModels.ReeFour.overlap m)
  · exact GreenBook.LieModels.ReeFour.overlap m

theorem native_lifts {m : ℕ} (hm : 0<m) (i : Bool) (a : Iso (amalgam m i) (amalgam m i)) :
    ∃ f : Model m →* Model m,
      (∀ x, f ((model m i).left x) = (model m i).left (a.left x)) ∧
      (∀ x, f ((model m i).right x) = (model m i).right (a.right x)) := by
  cases i
  · obtain ⟨f,hl,hr⟩ := exists_native_action_extension hm a
    exact ⟨f.toMonoidHom,hl,hr⟩
  · obtain ⟨f,hl,hr⟩ := exists_native_action_extension hm a.reverse
    exact ⟨f.toMonoidHom,hr,hl⟩

theorem parabolic_normalizer (m : ℕ) (s : Side) :
    normalizer (ReeF4.Parabolics.parabolic m s : Set (Model m)) =
      ReeF4.Parabolics.parabolic m s := by
  apply NativeRestoration.self_normalizing_of_sylow (GreenBook.LieModels.ReeFour.sylow m)
  · exact (GreenBook.LieModels.ReeFour.sylow_le_localFactor m s).trans
      (localFactor_le_parabolic m s)
  · rw [GreenBook.LieModels.ReeFour.sylow_normalizer]
    exact borel_le_parabolic m s

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) (m : ℕ) (i : Bool)
  (e : Iso (reducedAmalgam L S) (amalgam m i))

abbrev reducedCompletion := (model m i).comapIso e

theorem reduced_preserved (hm : 0<m) :
    PreservesCompletionKernel h (reducedCompletion m i e) :=
  NativeRestoration.preserves_of_native_lifts (reducedOverlapAction h) e (model m i)
    (native_lifts hm i)

theorem reduced_overlap :
    (reducedCompletion m i e).left.range ⊓ (reducedCompletion m i e).right.range =
      (reducedCompletion m i e).middle.range := by
  simp only [reducedCompletion, FaithfulCompletion.comapIso_left_range,
    FaithfulCompletion.comapIso_right_range, FaithfulCompletion.comapIso_middle_range]
  exact model_overlap m i

theorem reduced_normalizer (j : Fin 2) :
    normalizer ((completionEndpoint (reducedCompletion m i e) j).range : Set (Model m)) =
      (completionEndpoint (reducedCompletion m i e) j).range := by
  fin_cases j
  · change normalizer ((reducedCompletion m i e).left.range : Set (Model m)) =
      (reducedCompletion m i e).left.range
    rw [FaithfulCompletion.comapIso_left_range,model_left_range]
    exact parabolic_normalizer m (side i)
  · change normalizer ((reducedCompletion m i e).right.range : Set (Model m)) =
      (reducedCompletion m i e).right.range
    rw [FaithfulCompletion.comapIso_right_range,model_right_range]
    exact parabolic_normalizer m (side (!i))

include h e in
/-- Odd outer degree kills the entire original extension. -/
theorem original_sylow_eq_reduced (hm : 0<m) :
    S = SuzukiContainment.reducedSylow L S :=
  NativeRestoration.sylow_eq_reduced_of_twoPower_inner h (reducedCompletion m i e)
    (reduced_preserved h m i e hm) (reduced_overlap m i e) (reduced_normalizer m i e)
    (OuterLocal.inner_of_twoPower m)

/-- Both original endpoints and the full original Borel are restored to the
native group; no original comparison or extension-collapse premise is needed. -/
def originalIso (hm : 0<m) : Iso (originalAmalgam L S) (amalgam m i) :=
  (NativeRestoration.originalIsoReduced (original_sylow_eq_reduced h m i e hm)).trans e

/-- Restoration restricts to the supplied reduced marking on all three
literal inclusions, including every element of the whole reduced Borel. -/
theorem originalIso_reduced (hm : 0<m) :
    (∀ x : Source.parabolic L (SuzukiContainment.reducedSylow L S) 0,
      (originalIso h m i e hm).left (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x) = e.left x) ∧
    (∀ x : commonBorel L (SuzukiContainment.reducedSylow L S),
      (originalIso h m i e hm).middle (inclusion (SuzukiContainment.reduced_commonBorel_le h) x) =
        e.middle x) ∧
    (∀ x : Source.parabolic L (SuzukiContainment.reducedSylow L S) 1,
      (originalIso h m i e hm).right (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x) = e.right x) :=
  NativeRestoration.originalIsoReduced_trans_reduced h
    (original_sylow_eq_reduced h m i e hm) e

include h e in
/-- The same original S lies in both source local factors. -/
theorem original_sylow_le_locals (hm : 0<m) : S ≤ L 0 ∧ S ≤ L 1 :=
  ⟨SuzukiContainment.sylow_le_local_of_ree_parabolic h 0 (by omega) (side i)
      (originalIso h m i e hm).left,
    SuzukiContainment.sylow_le_local_of_ree_parabolic h 1 (by omega) (side (!i))
      (originalIso h m i e hm).right⟩

/-- Literal F.1.12 application: retain the actual ambient Sylow T and the
same right factor R from the original linear/Suzuki pair. -/
theorem original_T_le_right {H : Type*} [Group H] [Finite H]
    {K R : Subgroup H} (T : Sylow 2 H)
    (hf : HypothesisF11 ![K,R] (T : Subgroup H))
    (m : ℕ) (i : Bool)
    (em : Iso (reducedAmalgam ![K,R] (T : Subgroup H)) (amalgam m i))
    (hm : 0<m) : (T : Subgroup H) ≤ R :=
  (original_sylow_le_locals hf m i em hm).2

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.ReeNative

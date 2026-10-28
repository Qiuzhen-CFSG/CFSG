module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.NativeRestoration
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.NativeLift
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.RestoredCompletion

/-!
# Original linear restoration from the marked reduced row

The proved native PSL₃ amalgam lift extends every compatible automorphism in
both orientations. Transport of this lift proves preservation of the actual
universal kernel. The native Sylow normalizer lies in both parabolics, so
Sylow conjugacy proves that both endpoint images are self-normalizing.
The original restoration construction therefore gives a faithful completion
in Aut(PSL₃(F)), retaining the full Borel and both reduced inclusions. Its
actors preserve the two geometric parabolic types, so the extension lies
in the actual diagram kernel. The outer index is the original Borel index.

For a perfect source right factor, solvable residuals also supply its exact
native marking. This removes that extra premise from the linear F.1.12
application. The scalar quotient is retained, including over field four.

Source: DGS, *Groups and Graphs* (1985), (15.2), pp.226–228, and
Aschbacher–Smith F.1.12, pp.263–264. A genuine marked reduced comparison and
|F|=2ⁿ with n>1 remain inputs; no original comparison, Cartan geometry,
kernel invariance, or endpoint-normalizer premise is assumed.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.LinearNative
open Matrix.PSL3 Matrix.PSL3.LinearThree
open SourceCompletion.LinearThreeEven
variable (F : Type*) [Field F] [Finite F]

/-- `false` places the point endpoint first; `true` places the line first. -/
def amalgam (i : Bool) : RankTwoAmalgam (SmallCompletion.parabolic F i)
    (Matrix.PSL3.LinearThree.borel F) (SmallCompletion.parabolic F (!i)) :=
  ofSubgroups _ _ _ (borel_le_parabolic F i) (borel_le_parabolic F (!i))

def model (i : Bool) : FaithfulCompletion (amalgam F i) (G := PSL(3,F)) :=
  FaithfulCompletion.ofSubgroups _ _ _ (borel_le_parabolic F i)
    (borel_le_parabolic F (!i)) (by
      cases i
      · exact parabolics_sup_eq_top F
      · change lineParabolic F ⊔ pointParabolic F = ⊤
        rw [sup_comm]
        exact parabolics_sup_eq_top F)

theorem model_left_range (i : Bool) : (model F i).left.range = SmallCompletion.parabolic F i :=
  FaithfulCompletion.ofSubgroups_left_range ..
theorem model_right_range (i : Bool) : (model F i).right.range = SmallCompletion.parabolic F (!i) :=
  FaithfulCompletion.ofSubgroups_right_range ..
theorem model_middle_range (i : Bool) : (model F i).middle.range = Matrix.PSL3.LinearThree.borel F :=
  FaithfulCompletion.ofSubgroups_middle_range ..

theorem model_overlap (i : Bool) :
    (model F i).left.range ⊓ (model F i).right.range = (model F i).middle.range := by
  rw [model_left_range, model_right_range, model_middle_range]
  cases i
  · exact GreenBook.LieModels.LinearThree.parabolic_intersection F
  · exact (inf_comm _ _).trans (GreenBook.LieModels.LinearThree.parabolic_intersection F)

theorem native_lifts [CharP F 2] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) (i : Bool)
    (a : Iso (amalgam F i) (amalgam F i)) :
    ∃ f : PSL(3,F) →* PSL(3,F),
      (∀ x, f ((model F i).left x) = (model F i).left (a.left x)) ∧
      (∀ x, f ((model F i).right x) = (model F i).right (a.right x)) := by
  cases i
  · exact ⟨(nativeLift F hF hn a).toMonoidHom,
      nativeLift_left F hF hn a, nativeLift_right F hF hn a⟩
  · exact ⟨(nativeReverseLiftHom F hF hn a).toMonoidHom,
      nativeReverseLift_left F hF hn a, nativeReverseLift_right F hF hn a⟩

theorem parabolic_normalizer {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n) (i : Bool) :
    normalizer (SmallCompletion.parabolic F i : Set PSL(3,F)) = SmallCompletion.parabolic F i := by
  apply NativeRestoration.self_normalizing_of_sylow (unipotentSylow F hn hF)
  · exact (unipotent_le_borel F).trans (borel_le_parabolic F i)
  · change normalizer (unipotent F : Set PSL(3,F)) ≤ _
    rw [normalizer_unipotent F hn hF]
    exact borel_le_parabolic F i

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) (i : Bool) (e : Iso (reducedAmalgam L S) (amalgam F i))

abbrev reducedCompletion := (model F i).comapIso e

theorem reduced_preserved [CharP F 2] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) :
    PreservesCompletionKernel h (reducedCompletion F i e) :=
  NativeRestoration.preserves_of_native_lifts (reducedOverlapAction h) e (model F i)
    (native_lifts F hF hn i)

theorem reduced_overlap :
    (reducedCompletion F i e).left.range ⊓ (reducedCompletion F i e).right.range =
      (reducedCompletion F i e).middle.range := by
  simp only [reducedCompletion, FaithfulCompletion.comapIso_left_range,
    FaithfulCompletion.comapIso_right_range, FaithfulCompletion.comapIso_middle_range]
  exact model_overlap F i

theorem reduced_normalizer {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n) (j : Fin 2) :
    normalizer ((completionEndpoint (reducedCompletion F i e) j).range : Set PSL(3,F)) =
      (completionEndpoint (reducedCompletion F i e) j).range := by
  fin_cases j
  · change normalizer ((reducedCompletion F i e).left.range : Set PSL(3,F)) =
      (reducedCompletion F i e).left.range
    rw [FaithfulCompletion.comapIso_left_range,model_left_range]
    exact parabolic_normalizer F hF hn i
  · change normalizer ((reducedCompletion F i e).right.range : Set PSL(3,F)) =
      (reducedCompletion F i e).right.range
    rw [FaithfulCompletion.comapIso_right_range,model_right_range]
    exact parabolic_normalizer F hF hn (!i)


variable [CharP F 2] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n)

/-- The restored group consists of regular, type-preserving automorphisms.
Both native endpoint types are fixed by the actual original Borel action. -/
theorem extension_regular :
    automorphismExtension h (reducedCompletion F i e) (reduced_preserved F h i e hF hn) ≤
      OuterExtensions.diagramTrivial F := by
  apply sup_le
  · rintro a ⟨g,rfl⟩
    exact (OuterExtensions.mem_diagramTrivial F _).mpr (fun b => ⟨g,rfl⟩)
  · rintro a ⟨b,rfl⟩
    have hl := completionAction_endpoint_range h (reducedCompletion F i e)
      (reduced_preserved F h i e hF hn) 0 b
    have hr := completionAction_endpoint_range h (reducedCompletion F i e)
      (reduced_preserved F h i e hF hn) 1 b
    change (reducedCompletion F i e).left.range.map _ = (reducedCompletion F i e).left.range at hl
    change (reducedCompletion F i e).right.range.map _ = (reducedCompletion F i e).right.range at hr
    rw [FaithfulCompletion.comapIso_left_range, model_left_range] at hl
    rw [FaithfulCompletion.comapIso_right_range, model_right_range] at hr
    apply (OuterExtensions.mem_diagramTrivial_iff F _).mpr
    cases i
    · refine ⟨⟨1, ?_⟩, ⟨1, ?_⟩⟩
      · rw [map_one]
        change (pointParabolic F).map _ = (pointParabolic F).map (MonoidHom.id _)
        rw [map_id]
        exact hl
      · rw [map_one]
        change (lineParabolic F).map _ = (lineParabolic F).map (MonoidHom.id _)
        rw [map_id]
        exact hr
    · refine ⟨⟨1, ?_⟩, ⟨1, ?_⟩⟩
      · rw [map_one]
        change (pointParabolic F).map _ = (pointParabolic F).map (MonoidHom.id _)
        rw [map_id]
        exact hr
      · rw [map_one]
        change (lineParabolic F).map _ = (lineParabolic F).map (MonoidHom.id _)
        rw [map_id]
        exact hl

/-- DGS 15.2 on a genuinely marked nonbinary linear reduced row, in either
orientation. Kernel invariance, full overlap, and endpoint normalizers have
all been discharged; the three original maps are retained. -/
theorem original_completion :
    ∃ d : FaithfulCompletion (originalAmalgam L S)
      (G := automorphismExtension h (reducedCompletion F i e)
        (reduced_preserved F h i e hF hn)),
      (∀ b : commonBorel L S, (d.middle b : MulAut PSL(3,F)) =
        completionAction h (reducedCompletion F i e) (reduced_preserved F h i e hF hn) b) ∧
      (∀ x : parabolic L (SuzukiContainment.reducedSylow L S) 0,
        (d.left (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x) : MulAut PSL(3,F)) =
          MulAut.conj (e.left x).val) ∧
      (∀ x : parabolic L (SuzukiContainment.reducedSylow L S) 1,
        (d.right (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x) : MulAut PSL(3,F)) =
          MulAut.conj (e.right x).val) :=
  exists_original_completion h (reducedCompletion F i e) (reduced_preserved F h i e hF hn)
    (reduced_overlap F i e) (reduced_normalizer F i e hF (by omega))

/-- The index counts the same original full Borel, with its odd part retained. -/
theorem original_outer_index_eq :
    (MulAut.innerSubgroup PSL(3,F)).relIndex
      (automorphismExtension h (reducedCompletion F i e) (reduced_preserved F h i e hF hn)) =
      (commonBorel L (SuzukiContainment.reducedSylow L S)).relIndex (commonBorel L S) :=
  original_outer_index h (reducedCompletion F i e) (reduced_preserved F h i e hF hn)
    (reduced_overlap F i e) (reduced_normalizer F i e hF (by omega))


omit [CharP F 2] in
include h hn hF in
/-- For a perfect selected right factor, the reduced marking of that factor
is forced by the actual solvable residual. No separate local-factor mark is
required by the application to a prepared perfect R. -/
theorem right_factor_marking (hp : Group.IsPerfect (L 1)) :
    ((L 1).subgroupOf (parabolic L (SuzukiContainment.reducedSylow L S) 1)).map
      (reducedCompletion F i e).right = OuterExtensions.localFactor F i := by
  let := hp
  let := h.finite_local 1
  let := (SuzukiContainment.reduced_hypothesis h).finite_parabolic 1
  have hloc : (L 1).subgroupOf (parabolic L (SuzukiContainment.reducedSylow L S) 1) =
      solvableResidual (parabolic L (SuzukiContainment.reducedSylow L S) 1) := by
    apply Subgroup.map_injective (parabolic L (SuzukiContainment.reducedSylow L S) 1).subtype_injective
    rw [map_subgroupOf_eq_of_le (show L 1 ≤ parabolic L (SuzukiContainment.reducedSylow L S) 1
      from le_sup_left.trans le_sup_left)]
    rw [← (SuzukiContainment.reduced_hypothesis h).local_residual_eq_parabolic 1,
      solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  rw [hloc]
  change (solvableResidual (parabolic L (SuzukiContainment.reducedSylow L S) 1)).map
    ((SmallCompletion.parabolic F (!i)).subtype.comp e.right.toMonoidHom) = _
  rw [← map_map, map_solvableResidual_eq _ e.right.surjective]
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2^2 ≤ 2^n from Nat.pow_le_pow_right (by decide) hn)
  cases i
  · exact ParabolicResiduals.lineParabolic_residual F hcard
  · exact ParabolicResiduals.pointParabolic_residual F hcard

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.LinearNative

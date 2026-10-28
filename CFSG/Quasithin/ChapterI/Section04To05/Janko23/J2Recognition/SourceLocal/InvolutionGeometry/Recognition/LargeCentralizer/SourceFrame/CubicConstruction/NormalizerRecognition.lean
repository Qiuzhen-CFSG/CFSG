module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.Identification
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.RootProduct
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.Action
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.Splitting

/-!
# Assembling the marked root-normalizer identification

Actual compatible lifts of the model actor give a homomorphism from the
explicit semidirect product to the full normalizer. Trivial intersection with
R proves injectivity, and generation of the full normalizer proves
surjectivity. Its restriction to the root coordinates is the literal subgroup
inclusion, so the inverse equivalence has exactly the marking required by
`NormalizerIdentification`.

The source core geometry constructs `RootAction`, and the Sylow--Frattini
argument constructs `SplitAction` from it. Combining these results identifies
the full normalizer of every returning pair from the seed and local census,
with no remaining coordinate, action or splitting premise. The existential
theorem supplies the marked identification required by the cubic-geometry
and pure-four centralizer consumers.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3 and 46.14,
printed pp.251 and 257–258.
-/

@[expose] public section

open Subgroup Matrix.PSL3Four

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition

variable {G : Type*} [Group G] [Finite G] {D : Seed G}
variable {P : ReturningPair D} {e : P.R ≃* RootNormalizerModel.Root}

namespace SplitAction

variable (S : SplitAction P e)

/-- Multiplication of the literal root inclusion and the actual actor lift. -/
noncomputable def modelMap :
    RootNormalizerModel.Model →* normalizer (P.R : Set G) :=
  SemidirectProduct.lift (rootEmbedding P e) S.lift S.compatible

theorem modelMap_inl (x : RootNormalizerModel.Root) :
    S.modelMap (SemidirectProduct.inl x) = rootEmbedding P e x :=
  SemidirectProduct.lift_inl _ _ _ _

theorem modelMap_inr (a : RootNormalizerModel.actor) :
    S.modelMap (SemidirectProduct.inr a) = S.lift a :=
  SemidirectProduct.lift_inr _ _ _ _

theorem modelMap_injective : Function.Injective S.modelMap := by
  apply S.modelMap.ker_eq_bot_iff.mp
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have hf : rootEmbedding P e x.left * S.lift x.right = 1 := hx
  have ha : S.lift x.right = (rootEmbedding P e x.left)⁻¹ := by
    calc
      _ = (rootEmbedding P e x.left)⁻¹ *
          (rootEmbedding P e x.left * S.lift x.right) := by group
      _ = _ := by rw [hf, mul_one]
  have hr : x.right = 1 := S.disjoint _ (by
    rw [ha]
    exact P.R.inv_mem (e.symm x.left).property)
  have hl : x.left = 1 := by
    apply rootEmbedding_injective P e
    simpa only [hr, map_one, mul_one] using hf
  exact SemidirectProduct.ext hl hr

theorem modelMap_surjective : Function.Surjective S.modelMap := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← S.generation]
  apply sup_le
  · rw [← rootEmbedding_range P e]
    rintro _ ⟨x, rfl⟩
    exact ⟨SemidirectProduct.inl x, S.modelMap_inl x⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨SemidirectProduct.inr a, S.modelMap_inr a⟩

noncomputable def modelEquiv : RootNormalizerModel.Model ≃* normalizer (P.R : Set G) :=
  MulEquiv.ofBijective S.modelMap ⟨S.modelMap_injective, S.modelMap_surjective⟩

theorem modelEquiv_root :
    RootNormalizerModel.root.map S.modelEquiv.toMonoidHom =
      P.R.subgroupOf (normalizer (P.R : Set G)) := by
  change RootNormalizerModel.root.map S.modelMap = _
  rw [RootNormalizerModel.root, ← MonoidHom.range_comp]
  have he : S.modelMap.comp SemidirectProduct.inl = rootEmbedding P e := by
    apply MonoidHom.ext
    intro x
    exact S.modelMap_inl x
  rw [he, rootEmbedding_range]

/-- The complement construction meets the published full-normalizer contract. -/
noncomputable def identification : NormalizerIdentification P where
  equiv := S.modelEquiv.symm
  root_eq := by
    apply le_antisymm
    · rintro x ⟨n, hn, rfl⟩
      rw [← S.modelEquiv_root] at hn
      obtain ⟨x, hx, rfl⟩ := hn
      change S.modelEquiv.symm (S.modelEquiv x) ∈ RootNormalizerModel.root
      rw [S.modelEquiv.symm_apply_apply]
      exact hx
    · intro x hx
      exact mem_map.mpr ⟨S.modelEquiv x,
        S.modelEquiv_root ▸ mem_map_of_mem S.modelEquiv.toMonoidHom hx,
        S.modelEquiv.symm_apply_apply x⟩

/-- The assembled equivalence preserves the specified root coordinates. -/
theorem identification_coordinates (r : P.R) :
    S.identification.equiv (inclusion le_normalizer r) =
      SemidirectProduct.inl (e r) := by
  apply S.modelEquiv.injective
  change S.modelEquiv (S.modelEquiv.symm _) = _
  rw [MulEquiv.apply_symm_apply]
  change inclusion le_normalizer r = S.modelMap (SemidirectProduct.inl (e r))
  rw [S.modelMap_inl]
  exact Subtype.ext (congrArg (fun r : P.R => (r : G)) (e.symm_apply_apply r)).symm

end SplitAction

/-- Conditional assembly retaining the two independent construction inputs.
The source-action producer only needs to construct one returning pair. -/
theorem exists_identification_of_action_and_splitting
    (hAction : ∃ P : ReturningPair D, Nonempty (RootAction P))
    (hSplit : ∀ (P : ReturningPair D) (A : RootAction P),
      Nonempty (SplitAction P A.coordinates)) :
    ∃ P : ReturningPair D, Nonempty (NormalizerIdentification P) := by
  obtain ⟨P, ⟨A⟩⟩ := hAction
  obtain ⟨S⟩ := hSplit P A
  exact ⟨P, ⟨S.identification⟩⟩

/-- The full normalizer of every source returning pair is the explicit split
extension of UT₃(F₄), with the literal root subgroup preserved. The source
action and actor-lifting theorems discharge both construction inputs. -/
theorem nonempty_identification (P : ReturningPair D) (L : LocalCensus D) :
    Nonempty (NormalizerIdentification P) := by
  obtain ⟨A⟩ := SourceAction.nonempty_rootAction P L
  obtain ⟨S⟩ := exists_splitAction P A
  exact ⟨S.identification⟩

/-- The source seed and local census supply the marked full-normalizer
identification of 46.14(1), including the actual action and splitting of
46.3. No normalizer-recognition premise remains. -/
theorem exists_identification (D : Seed G) (L : LocalCensus D) :
    ∃ P : ReturningPair D, Nonempty (NormalizerIdentification P) :=
  exists_identification_of_action_and_splitting
    (SourceAction.exists_rootAction D L) (fun P A => exists_splitAction P A)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition

module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.Action
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction

/-!
# Rank-one exclusions for the moved component quotient

The flag residual remains a local C-component after restriction to its
containing normal component and projection modulo that component's two-core.
Its image is proper: otherwise every quotient automorphism would preserve it,
contrary to the actual odd supplement action. The Bender containment theorem
therefore excludes all three Bender families and every even SU₃ cover.

The final application supplies these exclusions from the original
Sylow-normalizer escape. The remaining component comparison and terminal
geometry stay with qt-d-1222-natural-line-action; this is not the complete
3.3.12 classification.

Source: Aschbacher--Smith, A.3.12 and the component comparison in 3.3.12,
printed pp.48 and 589--590.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
open ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The actual moved residual has proper image in the component quotient. -/
theorem residualImage_ne_top : E.residualImage ≠ ⊤ := by
  intro he
  apply E.oddAction_moves
  intro a _
  change E.residualImage.map a.toMonoidHom = E.residualImage
  rw [he,map_top_of_surjective _ a.surjective]

/-- Restriction and two-core projection preserve the literal local component. -/
theorem residualImage_local : E.residualImage ∈ localCComponents E.quotientSylow := by
  have hlocal := (Components.flag_mem_local_of_model D S f E.index
    ((invariantFlag_geometry D S f).2.2.model E.index)).1
  have hres := SourceEmbeddings.local_restrict hlocal E.contains.le
  let q := QuotientGroup.mk' (pCore 2 E.component)
  let : Group.IsNilpotent (pCore 2 E.component) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hres q

/-- The top subgroup of the containing component quotient is a C-component. -/
theorem componentQuotient_isCComponent :
    (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)).IsCComponent := by
  have ht : (⊤ : Subgroup E.component).IsCComponent := by
    simpa only [subgroupOf_self] using
      E.normal_component.1.2.subgroupOf_of_le le_rfl E.normal_component.1.1
  let : Group.IsNilpotent (pCore 2 E.component) := pCore_isPGroup.isNilpotent
  simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
    ht.map_quotient (pCore 2 E.component)

/-- No Bender model admits this proper local C-component. -/
theorem quotient_not_bender :
    ¬ ClassificationModels.IsBenderModel (E.component ⧸ pCore 2 E.component) := by
  intro hm
  obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
  have hlocal : E.residualImage ∈ localCComponents P := hP.symm ▸ E.residualImage_local
  have hmodel : ClassificationModels.IsBenderModel
      (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := hm.of_mulEquiv topEquiv
  exact E.residualImage_ne_top (SourceEmbeddings.eq_of_bender_containing_component
    P hlocal E.componentQuotient_isCComponent le_top hmodel)

/-- The same exclusion retains the full even special-unitary cover. -/
theorem quotient_not_binary_su3 {n : ℕ} (hn : 0 < n) :
    ¬ Chapter1.Section02.LocalModels.IsSU (E.component ⧸ pCore 2 E.component) 3 (2^n) := by
  rintro ⟨F,hF,hfin,J,hcard,hcompat,⟨e⟩⟩
  obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
  have hlocal : E.residualImage ∈ localCComponents P := hP.symm ▸ E.residualImage_local
  exact E.residualImage_ne_top (SourceEmbeddings.eq_of_binary_su3_containing_component
    P hlocal E.componentQuotient_isCComponent le_top hn
    ⟨F,hF,hfin,J,hcard,hcompat,⟨topEquiv.trans e⟩⟩)

end MovedComponent

/-- The original normalizer escape supplies a proper local residual and rules
out all rank-one containing models, using the original quotient and Sylow. -/
theorem exists_moved_component_not_rank_one (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      E.residualImage ∈ localCComponents E.quotientSylow ∧ E.residualImage ≠ ⊤ ∧
      ¬ ClassificationModels.IsBenderModel (E.component ⧸ pCore 2 E.component) ∧
      ∀ n : ℕ, 0 < n →
        ¬ Chapter1.Section02.LocalModels.IsSU (E.component ⧸ pCore 2 E.component) 3 (2^n) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E, E.residualImage_local, E.residualImage_ne_top, E.quotient_not_bender,
    fun _ hn => E.quotient_not_binary_su3 hn⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

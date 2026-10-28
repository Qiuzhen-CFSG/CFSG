module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.PairGeometry

/-!
# The actual source witnesses for 15.4.19

Choose the two source pairs from their original faithful actions and keep both
inside one raw Geometry. Its J, Z and V(M) are the literal Thompson subgroup,
central omega and original normal-closure modules. The factor actions follow
from the selected pairs and the earlier whole-module statements of 15.4.12.

The fixed-space calculation proves all three clauses of 15.4.19 for all four
factor choices. The same source Sylow supplement and cubic factor quotients
give index three, the actual local Sylow images and G₁ ∩ G₂ = T₀. Only the
original preceding source hypotheses remain explicit; no LocalData, fixed
hyperplane, common central subgroup or intersection conclusion is assumed.

Source: Aschbacher–Smith, 15.4.12 and 15.4.19, printed pp.1160–1163.
The full overgroup-Sylow conclusion 15.4.20 remains separate.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

/-- The source Geometry, retaining both choices of each actually constructed factor. -/
noncomputable def geometry (pX : Pair T M₁ X) (pY : Pair T M₂ Y) : Source.Geometry G where
  T := T
  X := pX.quotient.factor
  Y := pY.quotient.factor
  J := ChapterB.thompsonJ (T : Subgroup G) 0
  Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  VM₁ := localV T M₁
  VM₂ := localV T M₂

/-- The actual uniform 15.4.19 conclusions and the ensuing local intersections.
This is an output proposition, not a hypothesis on the source configuration. -/
structure Conclusions (d : Source.Geometry G) : Prop where
  outside_X : ∀ i, ¬ d.X i ≤ d.M₂
  outside_Y : ∀ j, ¬ d.Y j ≤ d.M₁
  central_geometry : ∀ i j,
    ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ centralizer (d.I i j : Set G) ≠ ⊥ ∧
    ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ centralizer (d.I i j : Set G) ≤
      (center (d.I i j)).map (d.I i j).subtype ∧
    d.I i j ∈ Chapter1.H G ∧
    d.Z ⊓ ((center (d.I i j)).map (d.I i j).subtype ⊔ d.V₁ i) ≠ ⊥
  index_X : ∀ i, d.T₀.relIndex (d.G₁ i) = 3
  sylow_X : ∀ i, ∃ Q : Sylow 2 (d.G₁ i),
    (Q : Subgroup (d.G₁ i)).map (d.G₁ i).subtype = d.T₀
  intersections : ∀ i j, d.G₁ i ⊓ d.G₂ j = d.T₀

/-- The literal same-pair application. Retaining the two Pair witnesses lets
the later Sylow argument reuse their original quotient maps and permutations. -/
theorem source_geometry_conclusions
    (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (earlierX : Earlier412 T M₁ X) (earlierY : Earlier412 T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥) :
    Conclusions (geometry pX pY) := by
  let d := geometry pX pY
  have ht : d.T = T := rfl
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hy : d.wholeY = Y := pY.quotient.factor_generate hY
  have hm₁ : d.M₁ = M₁ := by change normalizer (d.wholeX : Set G) = M₁; rw [hx, hM₁]
  have hm₂ : d.M₂ = M₂ := by change normalizer (d.wholeY : Set G) = M₂; rw [hy, hM₂]
  have hSX : ChapterB.baumann (d.T : Subgroup G) ≤ normalizer (d.X false : Set G) := pX.baumann false
  have hSY : ChapterB.baumann (d.T : Subgroup G) ≤ normalizer (d.Y false : Set G) := pY.baumann false
  have hS : ChapterB.baumann (d.T : Subgroup G) ≤ d.T₀ := le_inf (le_inf inf_le_left hSX) hSY
  have hTX : (d.T : Subgroup G) ≤ d.M₁ := hm₁.symm ▸ hX.sylow_le
  have hTY : (d.T : Subgroup G) ≤ d.M₂ := hm₂.symm ▸ hY.sylow_le
  have hgenX (i) : d.X i ⊔ (d.T : Subgroup G) = d.wholeX ⊔ (d.T : Subgroup G) := by
    rw [hx]
    exact pX.factor_join_sylow hX i
  have hgenY (i) : d.Y i ⊔ (d.T : Subgroup G) = d.wholeY ⊔ (d.T : Subgroup G) := by
    rw [hy]
    exact pY.factor_join_sylow hY i
  have huX : ∀ M : Subgroup G, IsMaximalTwoLocal M → d.wholeX ⊔ (d.T : Subgroup G) ≤ M → M = d.M₁ := by
    simpa only [hx, hm₁, ht] using huniqueX
  have huY : ∀ M : Subgroup G, IsMaximalTwoLocal M → d.wholeY ⊔ (d.T : Subgroup G) ≤ M → M = d.M₂ := by
    simpa only [hy, hm₂, ht] using huniqueY
  have hz : d.Z = Stellmacher.omegaOneCenterAmbient (d.T : Subgroup G) := rfl
  have hcz : d.Z ⊓ centralizer (d.wholeX : Set G) ≠ ⊥ := by rw [hx]; exact hCZ
  have hnX₀ : d.T₀ ≤ normalizer (pX.quotient.factor false : Set G) := inf_le_left.trans inf_le_right
  have hnY₀ : d.T₀ ≤ normalizer (pY.quotient.factor false : Set G) := inf_le_right
  have haX := pX.factor_actions hX earlierX d.T₀_le_T hnX₀
  have haY := pY.factor_actions hY earlierY d.T₀_le_T hnY₀
  obtain ⟨houtX, houtY, hgeom⟩ := central_geometry_from_factor_actions d hz hZcard hcz hS
    hTX hTY (hm₁.symm ▸ hX.maximal) (hm₂.symm ▸ hY.maximal) hgenX hgenY huX huY
    (by simpa only [hm₁, hm₂] using hne) (fun side => by cases side; exact haX; exact haY)
  have hnX (i) : d.T₀ ≤ normalizer (d.X i : Set G) := by
    have hpair := pX.quotient.action
    intro t ht
    let m : M₁ := ⟨t, hX.sylow_le (d.T₀_le_T ht)⟩
    have hf : hpair.permutation m false = false := hpair.distinct
      ((hpair.conjugation m false).symm.trans (mem_normalizer_iff_map_conj_eq.mp (hnX₀ ht)))
    have hi : hpair.permutation m i = i := by
      cases i
      · exact hf
      · cases he : hpair.permutation m true
        · exact False.elim (Bool.false_ne_true ((hpair.permutation m).injective (hf.trans he.symm)))
        · rfl
    exact mem_normalizer_iff_map_conj_eq.mpr ((hpair.conjugation m i).trans (congrArg d.X hi))
  have hPs : ∃ P : Sylow 2 (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G),
      (P : Subgroup (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G)).map
        (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G).subtype =
          ChapterB.baumann (d.T : Subgroup G) := by
    rw [hx, ht]
    exact earlierX.sylow
  obtain ⟨P, hP⟩ := hPs
  have hindices := factor_intersections_from_source_quotients d hS hnX
    (fun i => pX.quotient.factor_quotient_card i) P hP hTY houtX
  exact ⟨houtX, houtY, hgeom, hindices.1, hindices.2.1, hindices.2.2⟩

/-- Construct the raw source Geometry and prove every clause of 15.4.19,
uniformly in both factor choices, with the literal triple intersections.
The retained source assumptions are the genuine preceding 15.4.12 and 15.4.14
outputs; the actual pair and all its module/action hypotheses are constructed. -/
theorem source_lemma_15_4_19
    (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (earlierX : Earlier412 T M₁ X) (earlierY : Earlier412 T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥) :
    ∃ d : Source.Geometry G,
      d.T = T ∧ d.wholeX = X ∧ d.wholeY = Y ∧ d.M₁ = M₁ ∧ d.M₂ = M₂ ∧
      d.J = ChapterB.thompsonJ (T : Subgroup G) 0 ∧
      d.Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ∧
      d.VM₁ = localV T M₁ ∧ d.VM₂ = localV T M₂ ∧ Conclusions d := by
  obtain ⟨pX⟩ := exists_pair hX
  obtain ⟨pY⟩ := exists_pair hY
  let d := geometry pX pY
  have ht : d.T = T := rfl
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hy : d.wholeY = Y := pY.quotient.factor_generate hY
  refine ⟨d, rfl, hx, hy, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · change normalizer (d.wholeX : Set G) = M₁
    rw [hx, hM₁]
  · change normalizer (d.wholeY : Set G) = M₂
    rw [hy, hM₂]
  · exact source_geometry_conclusions hX hY pX pY earlierX earlierY hM₁ hM₂ huniqueX huniqueY hne hZcard hCZ

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses

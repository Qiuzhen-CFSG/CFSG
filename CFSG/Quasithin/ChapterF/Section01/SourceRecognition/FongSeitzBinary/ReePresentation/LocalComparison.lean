module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceSuzukiPresentation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReePresentation.RankOne

/-!
# Local Suzuki presentation on original and geometric markings

The conditional local presentation comparison is restricted along the exact
original endpoint map supplied by the marked amalgam. Endpoint injectivity
and the already proved unique lift give an actual isomorphism of original
local subgroups, with the literal root formula and endpoint square. The
common-Borel formula retains the same original overlap map on its intersection
with this local subgroup. The construction applies to both original and
universal/geometric quotient markings.

This is the root--full-Cartan--reflection subgroup, not an entire endpoint or
common Borel. Full relative-root assembly is still needed for the Chapter12
comparison. Source: DGS, *Groups and Graphs*, Theorem D, p.224;
Aschbacher--Smith F.1.1, pp.259--260; Steinberg Section 11, Lemmas 62--64.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i : Fin 2) (n : Q.tits.N)
  {m : ℕ} (d : SourceRankOne.SuzukiData Q split i n m)
  (r : SourceSuzukiPresentation.Relations Q split i n d)

/-- Restriction of the literal original/geometric endpoint map. -/
def originalLocalMap : localSubgroup Q e split i n →*
    SourceRankOne.generated Q split i n :=
  ((MarkedLocal.endpointMap Q e i).comp (localSubgroup Q e split i n).subtype).codRestrict _
    (fun a => a.property)

@[simp] theorem originalLocalMap_apply (a : localSubgroup Q e split i n) :
    (originalLocalMap Q e split i n a : X ⧸ Q.D) = MarkedLocal.endpointMap Q e i a := rfl

/-- The source quotient remains injective on the entire original local subgroup. -/
theorem originalLocalMap_injective : Function.Injective (originalLocalMap Q e split i n) := by
  intro a b hab
  apply Subtype.ext
  apply (MarkedLocal.endpoint Q e i).injective
  have he : MarkedLocal.endpointMap Q e i a = MarkedLocal.endpointMap Q e i b :=
    congrArg (fun z : SourceRankOne.generated Q split i n => (z : X ⧸ Q.D)) hab
  exact Subtype.ext he

include d in
theorem originalLocalMap_surjective : Function.Surjective (originalLocalMap Q e split i n) := by
  intro y
  obtain ⟨a,ha,_⟩ := existsUnique_original_lift Q e split i n d y y.property
  refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
  change MarkedLocal.endpointMap Q e i a ∈ SourceRankOne.generated Q split i n
  rw [ha]
  exact y.property

/-- An actual comparison on the original local subgroup, using the same
quotient, full Cartan and selected endpoint. This also applies to the universal/geometric marking. -/
def originalLocalComparison : localSubgroup Q e split i n ≃* SuzukiPresentation.generated m :=
  (MulEquiv.ofBijective (originalLocalMap Q e split i n)
    ⟨originalLocalMap_injective Q e split i n,originalLocalMap_surjective Q e split i n d⟩).trans
    (SourceSuzukiPresentation.comparison Q split i n d r)

/-- The endpoint square uses exactly the existing endpointMap, not a fresh projection. -/
theorem originalLocalComparison_square (a : localSubgroup Q e split i n) :
    originalLocalComparison Q e split i n d r a =
      SourceSuzukiPresentation.comparison Q split i n d r
        ⟨MarkedLocal.endpointMap Q e i a,a.property⟩ := rfl

/-- Original roots are sent to the exact native negative Suzuki word. -/
theorem originalLocalComparison_root (a : localSubgroup Q e split i n)
    (v : ReeF4.CoefficientField m × ReeF4.CoefficientField m)
    (ha : MarkedLocal.endpointMap Q e i a = d.chart v) :
    (originalLocalComparison Q e split i n d r a : ReeF4.Model m) = suzuki m false v.1 v.2 := by
  rw [originalLocalComparison_square]
  have he : (⟨MarkedLocal.endpointMap Q e i a,a.property⟩ : SourceRankOne.generated Q split i n) =
      ⟨d.chart v,ha ▸ a.property⟩ := Subtype.ext ha
  rw [he]
  exact SourceSuzukiPresentation.comparison_root Q split i n d r v _

/-- The same original overlap map controls the restriction of the local comparison. -/
theorem originalLocalComparison_borel (h : HypothesisF11 L S) (b : commonBorel L S)
    (hb : MarkedLocal.borelMap Q e h b ∈ SourceRankOne.generated Q split i n) :
    ∃ a : localSubgroup Q e split i n,
      (a.val : G) = b ∧ originalLocalComparison Q e split i n d r a =
        SourceSuzukiPresentation.comparison Q split i n d r ⟨MarkedLocal.borelMap Q e h b,hb⟩ := by
  obtain ⟨a,ha,he⟩ := local_borel_formula Q e split i n h b hb
  refine ⟨a,ha,?_⟩
  rw [originalLocalComparison_square]
  exact congrArg (SourceSuzukiPresentation.comparison Q split i n d r) (Subtype.ext he)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation

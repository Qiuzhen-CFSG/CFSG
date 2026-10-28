module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CommonCover
/-!
# Path transitivity in the actual full Ree completion

The canonical inclusion in the full binary Ree group and any faithful source
completion receive coverings from the same actual group pushout. Their rooted
nonbacktracking actions therefore have exactly the same transitivity at both
marked vertex types and every length. The maps preserve the given Suzuki and
linear inclusions. Translating the standard roots covers every source vertex.

This isolates the concrete model path theorem needed by F.4.6 from the source
completion transport. No braid, polygon, or recognition assertion is assumed.

Source: Aschbacher--Smith, F.3.3--4 and F.4.6(1), printed pp.270 and 276.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
local notation "α" => Tits.ExceptionalParabolics.FullRee.amalgam

def modelCompletion : Completion (ReeF4.Model 0) :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups
    Tits.ExceptionalParabolics.FullRee.first Tits.ExceptionalParabolics.FullRee.B
    Tits.ExceptionalParabolics.FullRee.second
    Tits.ExceptionalParabolics.FullRee.borel_le_first
    Tits.ExceptionalParabolics.FullRee.borel_le_second
    Tits.ExceptionalParabolics.FullRee.generate

def modelFamily : Bool → Subgroup (ReeF4.Model 0) :=
  fun i => bif i then Tits.ExceptionalParabolics.FullRee.second
    else Tits.ExceptionalParabolics.FullRee.first

@[simp] theorem modelCompletion_family : modelCompletion.family = modelFamily := by
  funext i
  cases i <;> simp [modelCompletion, Completion.family, modelFamily]

private theorem gcd_model :
    (Nat.card Tits.ExceptionalParabolics.FullRee.first).gcd
      (Nat.card Tits.ExceptionalParabolics.FullRee.second) =
        Nat.card Tits.ExceptionalParabolics.FullRee.B := by
  rw [Tits.ExceptionalParabolics.FullRee.first_card,
    Tits.ExceptionalParabolics.FullRee.second_card,
    Tits.ExceptionalParabolics.FullRee.borel_card]
  norm_num

variable {G : Type*} [Group G] (c : Completion G)
namespace Completion

/-- The canonical common cover comes from the actual pushout of the marked
full Ree amalgam, not from an assumed comparison homomorphism between completions. -/
theorem rootPathTransitive_iff_model (i : Bool) (n : ℕ) :
    RootPathTransitive c.graph G (base c.family i) n ↔
      RootPathTransitive (Subgroup.CosetGeometry.RankTwo.graph modelFamily) (ReeF4.Model 0) (base modelFamily i) n := by
  have h := RankTwoAmalgam.Universal.rootPathTransitive_iff α gcd_model c modelCompletion i n
  change RootPathTransitive c.graph G (base c.family i) n ↔
    RootPathTransitive modelCompletion.graph (ReeF4.Model 0) (base modelCompletion.family i) n at h
  unfold Completion.graph at h
  rw [modelCompletion_family] at h
  exact h

/-- A model theorem at both standard types supplies the same path transitivity
at every actual source vertex. In F.4.6 this is applied with length nine. -/
theorem all_rootPathTransitive_of_model (n : ℕ)
    (ht : ∀ i, RootPathTransitive (Subgroup.CosetGeometry.RankTwo.graph modelFamily) (ReeF4.Model 0) (base modelFamily i) n) :
    ∀ v : c.Vertex, RootPathTransitive c.graph G v n := by
  intro v
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base c.family v
  have hbase := (rootPathTransitive_iff_model c v.type n).mpr (ht v.type)
  have h := RootPathTransitive.smul c.graphAction hbase g
  simpa only [hg] using h
end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee

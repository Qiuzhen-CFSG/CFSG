module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.PointedCoefficients
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.Census
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Exclusions

/-!
# Small faithful full binary Ree completions

The original smallness witness produces a marked apartment and adjacent
reflection involutions. The actual endpoint census places this pair in one
of four common-Borel conjugacy orbits. The three nonstandard eighth-power
relations contradict checked local word certificates, so the canonical Weyl
braid holds. The checked Parrott presentation and Borel extension then identify
the entire completion with the full binary Ree group, preserving both original
endpoint maps and the common Borel.

This is the full binary Ree specialization of Aschbacher--Smith F.4.8, printed
p.278, used by J.4.7, printed pp.442--445. All geometry and finite local inputs
are supplied by their concrete producers; no recognition or order hypothesis
is added to the faithful completion and its literal smallness witness.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Theory.GroupTheory
namespace Completion
variable {G : Type*} [Group G] (c : Completion G)

theorem canonicalBraid_of_small (hsmall : c.Small) :
    Tits.ExceptionalParabolics.FullRee.CompletionPresentation.CanonicalBraid c := by
  apply PointedCoefficients.canonicalBraid_of_census_and_exclusions c hsmall
  · intro x y hx hy hnx hny hx2 hy2
    exact Tits.AmalgamRigidity.FullRee.PointedPairs.reflection_pair_conjugate
      x y hx hy hnx hny hx2 hy2
  · exact Tits.AmalgamRigidity.FullRee.BadBraid.bad_braid_shifted c
  · exact Tits.AmalgamRigidity.FullRee.BadBraid.bad_braid_twisted c
  · exact Tits.AmalgamRigidity.FullRee.BadBraid.bad_braid_twisted_shifted c

/-- Full F.4.8 for the original small binary Ree faithful completion. -/
def equivOfSmall (hsmall : c.Small) : G ≃* ReeF4.Model 0 :=
  canonicalEquiv c (canonicalBraid_of_small c hsmall)

@[simp] theorem equivOfSmall_left (hsmall : c.Small)
    (x : Tits.ExceptionalParabolics.FullRee.first) : equivOfSmall c hsmall (c.left x) = x :=
  canonicalEquiv_left c _ x

@[simp] theorem equivOfSmall_right (hsmall : c.Small)
    (x : Tits.ExceptionalParabolics.FullRee.second) : equivOfSmall c hsmall (c.right x) = x :=
  canonicalEquiv_right c _ x

@[simp] theorem equivOfSmall_middle (hsmall : c.Small)
    (x : Tits.ExceptionalParabolics.FullRee.B) : equivOfSmall c hsmall (c.middle x) = x :=
  canonicalEquiv_middle c _ x

theorem equivOfSmall_left_map (hsmall : c.Small) :
    c.left.range.map (equivOfSmall c hsmall).toMonoidHom = Tits.ExceptionalParabolics.FullRee.first :=
  canonicalEquiv_left_map c _

theorem equivOfSmall_right_map (hsmall : c.Small) :
    c.right.range.map (equivOfSmall c hsmall).toMonoidHom = Tits.ExceptionalParabolics.FullRee.second :=
  canonicalEquiv_right_map c _

theorem equivOfSmall_middle_map (hsmall : c.Small) :
    c.middle.range.map (equivOfSmall c hsmall).toMonoidHom = Tits.ExceptionalParabolics.FullRee.B :=
  canonicalEquiv_middle_map c _

theorem card_of_small (hsmall : c.Small) : Nat.card G = 35942400 :=
  (Nat.card_congr (equivOfSmall c hsmall).toEquiv).trans Tits.ExceptionalParabolics.FullRee.group_card

end Completion
variable {G : Type*} [Group G]

/-- J.4.7 source boundary with all three original subgroup marks retained. -/
theorem ofSource_recognition (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂)
    (hgen : P₁ ⊔ P₂ = ⊤)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂)
      Tits.ExceptionalParabolics.FullRee.amalgam)
    (hsmall : (ofSource P₁ T P₂ h₁ h₂ hgen e).Small) :
    ∃ E : G ≃* ReeF4.Model 0,
      P₁.map E.toMonoidHom = Tits.ExceptionalParabolics.FullRee.first ∧
      T.map E.toMonoidHom = Tits.ExceptionalParabolics.FullRee.B ∧
      P₂.map E.toMonoidHom = Tits.ExceptionalParabolics.FullRee.second :=
  ofSource_recognition_of_canonical_braid P₁ T P₂ h₁ h₂ hgen e
    (Completion.canonicalBraid_of_small _ hsmall)

/-- The two literal original-source geodesics discharge smallness and give full recognition. -/
theorem ofSource_recognition_of_two_geodesics
    (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂) (hgen : P₁ ⊔ P₂ = ⊤)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂)
      Tits.ExceptionalParabolics.FullRee.amalgam)
    (x y : Subgroup.CosetGeometry.RankTwo.Vertex (fun i => bif i then P₂ else P₁))
    (hd : (Subgroup.CosetGeometry.RankTwo.graph (fun i => bif i then P₂ else P₁)).dist x y = 8)
    (p q : (Subgroup.CosetGeometry.RankTwo.graph (fun i => bif i then P₂ else P₁)).Walk x y)
    (hp : p.length = 8) (hq : q.length = 8) (hpq : p ≠ q) :
    ∃ E : G ≃* ReeF4.Model 0,
      P₁.map E.toMonoidHom = Tits.ExceptionalParabolics.FullRee.first ∧
      T.map E.toMonoidHom = Tits.ExceptionalParabolics.FullRee.B ∧
      P₂.map E.toMonoidHom = Tits.ExceptionalParabolics.FullRee.second :=
  ofSource_recognition P₁ T P₂ h₁ h₂ hgen e
    (ofSource_small P₁ T P₂ h₁ h₂ hgen e x y hd p q hp hq hpq)

end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee

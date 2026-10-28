module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2Presentation.Weyl
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.EndpointIndices
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticFourPresentation.Positive

/-!
# C₂ Weyl and Cartan maps on the original amalgam

The common Borel map transports the internally proved two-parameter
coroot homomorphism back through the original middle marking. The two
commuting squares are the literal original endpoint maps. The same marking
places each simple Weyl word in its correctly oriented original endpoint.
This supplies useful marked data before global presentation faithfulness;
no unknown quotient model or source classification is assumed.

Source: Aschbacher–Smith F.1.1, printed pp.259–260; Steinberg §6,
pp.69–74.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticFourPresentation
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (d : C2Presentation.RootData (F := F) Q split)

/-- Both coroot parameters lifted to the full ORIGINAL common subgroup. -/
def originalTorusHom : (Fˣ × Fˣ) →* ↥(parabolic L S 0 ⊓ parabolic L S 1) :=
  e.middle.symm.toMonoidHom.comp d.borelTorusHom

/-- The middle marking sends the original torus to its literal quotient words. -/
theorem originalTorus_middle (p : Fˣ × Fˣ) :
    (e.middle (originalTorusHom Q e split d p) : X ⧸ Q.D) = d.torusPairHom p := by
  simp [originalTorusHom]

/-- The first original endpoint square, for the SAME two-parameter torus. -/
theorem originalTorus_left (p : Fˣ × Fˣ) :
    (e.left (inclusion (show parabolic L S 0 ⊓ parabolic L S 1 ≤ parabolic L S 0 from inf_le_left) (originalTorusHom Q e split d p)) : X ⧸ Q.D) =
      d.torusPairHom p := by
  have he := congrArg Subtype.val (e.left_commutes (originalTorusHom Q e split d p))
  rw [RootCoordinates.standardAmalgam_left_eq_inclusion Q] at he
  exact he.trans (originalTorus_middle Q e split d p)

/-- The second original endpoint square retains the entire common torus map. -/
theorem originalTorus_right (p : Fˣ × Fˣ) :
    (e.right (inclusion (show parabolic L S 0 ⊓ parabolic L S 1 ≤ parabolic L S 1 from inf_le_right) (originalTorusHom Q e split d p)) : X ⧸ Q.D) =
      d.torusPairHom p := by
  have he := congrArg Subtype.val (e.right_commutes (originalTorusHom Q e split d p))
  rw [RootCoordinates.standardAmalgam_right_eq_inclusion Q] at he
  exact he.trans (originalTorus_middle Q e split d p)

/-- Long-root Weyl words belong to the original first endpoint. -/
def originalLongWeyl (t : Fˣ) : parabolic L S 0 :=
  e.left.symm ⟨d.weylWord 1 t, d.weylWord_mem 1 t⟩

/-- Short-root Weyl words belong to the original second endpoint. -/
def originalShortWeyl (t : Fˣ) : parabolic L S 1 :=
  e.right.symm ⟨d.weylWord 0 t, d.weylWord_mem 0 t⟩

theorem originalLongWeyl_map (t : Fˣ) :
    (e.left (originalLongWeyl Q e split d t) : X ⧸ Q.D) = d.weylWord 1 t := by
  simp [originalLongWeyl]

theorem originalShortWeyl_map (t : Fˣ) :
    (e.right (originalShortWeyl Q e split d t) : X ⧸ Q.D) = d.weylWord 0 t := by
  simp [originalShortWeyl]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticFourPresentation

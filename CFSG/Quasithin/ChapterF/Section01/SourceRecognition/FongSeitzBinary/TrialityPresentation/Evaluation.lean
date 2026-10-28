module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.BruhatCover
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.Presentation

/-!
# Universal presentation evaluation on the original source quotient

The explicit source relations construct a surjective homomorphism from the
finite triality presentation to the literal `X / Q.D`. All twelve root maps
retain their original cubic or fixed-field parameters through the supplied
compatible scalar marking. The whole positive subgroup maps onto `split.U`,
and the presentation Borel maps into the complete source Borel.

The same quotient projection is retained for every original representative.
The carrier-general overlap application also accepts a geometric amalgam
marking, without assuming any universal-to-original-group descent. This is an
evaluation theorem, not model recognition: native relation verification and
both parabolic comparisons remain necessary for final source assembly.

Source: GLS3 2.3.5, 2.4.7–8; DGS Theorem D, printed p.224.
-/

@[expose] public noncomputable section
open Theory.GroupTheory Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
variable {X F : Type*} [Group X] [Field F] {Psrc : Fin 2 → Subgroup X}
variable {Q : MarkedQuotient Psrc} {split : SplitData Q.tits}
variable {m : ℕ} {hm : 0 < m} {σ : F ≃+* F}
namespace BruhatRootData
variable {d : PositiveRootData Q split m hm σ} (b : BruhatRootData d)

/-- The relations construct this map to the literal quotient; it is not supplied as input. -/
def presentationHom : Presentation.Universal m hm →* X ⧸ Q.D :=
  Presentation.lift b.signed.roots b.relations

theorem presentationHom_surjective : Function.Surjective b.presentationHom :=
  Presentation.lift_surjective b.signed.roots b.relations b.generates

theorem presentationHom_short (s : Bool) (i : Fin 3) (t : F) :
    b.presentationHom (Presentation.roots.shortSigned s i (d.scalars.extension t)) =
      if s then d.shortRoot i (.ofAdd t) else b.signed.negativeShort i (.ofAdd t) := by
  rw [presentationHom, Presentation.lift_short]
  cases s
  · change b.signed.negativeShort i (.ofAdd (d.scalars.extension.symm (d.scalars.extension t))) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  · exact d.scalars.positiveRoots_short d.shortRoot d.longRoot i t

theorem presentationHom_long (s : Bool) (i : Fin 3)
    (t : ScalarMarking.SourceFixed (σ := σ)) :
    b.presentationHom (Presentation.roots.longSigned s i (d.scalars.fixed t)) =
      if s then d.longRoot i (.ofAdd t) else b.signed.negativeLong i (.ofAdd t) := by
  rw [presentationHom, Presentation.lift_long]
  cases s
  · change b.signed.negativeLong i (.ofAdd (d.scalars.fixed.symm (d.scalars.fixed t))) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  · exact d.scalars.positiveRoots_long d.shortRoot d.longRoot i t

theorem presentationHom_nA (t) : b.presentationHom (Presentation.roots.nA t) = b.signed.roots.nA t :=
  Presentation.lift_nA _ _ _

theorem presentationHom_nB (t) : b.presentationHom (Presentation.roots.nB t) = b.signed.roots.nB t :=
  Presentation.lift_nB _ _ _

theorem presentationHom_torus (p) : b.presentationHom (Presentation.roots.torus p) = b.signed.roots.torus p :=
  Presentation.lift_torus _ _ _

theorem presentationHom_factor (i : Fin 6) (v : PositiveParameters m hm) :
    b.presentationHom (Presentation.roots.positive.factor i v) = b.signed.roots.positive.factor i v := by
  fin_cases i <;> first
    | exact Presentation.lift_short b.signed.roots b.relations true _ _
    | exact Presentation.lift_long b.signed.roots b.relations true _ _

theorem presentationHom_product (v : PositiveParameters m hm) :
    b.presentationHom (Presentation.roots.positive.product v) = b.signed.roots.positive.product v := by
  simp only [PositiveRoots.product, map_list_prod, List.map_ofFn, Function.comp_def,
    b.presentationHom_factor]

/-- The image of the whole positive subgroup is the exact source U. -/
theorem presentationHom_positive_image :
    Presentation.roots.positive.positiveClosure.map b.presentationHom = split.U := by
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨v,rfl⟩ := (Presentation.roots.positive.mem_positiveClosure_iff
      Presentation.positiveRelations x).mp hx
    rw [b.presentationHom_product]
    rw [← d.positive]
    exact (d.roots.mem_positiveClosure_iff d.root_relations _).mpr ⟨v,rfl⟩
  · intro hg
    rw [← d.positive] at hg
    obtain ⟨v,rfl⟩ := (d.roots.mem_positiveClosure_iff d.root_relations g).mp hg
    exact ⟨Presentation.roots.positive.product v,
      (Presentation.roots.positive.mem_positiveClosure_iff Presentation.positiveRelations _).mpr ⟨v,rfl⟩,
      b.presentationHom_product v⟩

/-- Both collected Borel factors map into the complete original source Borel. -/
theorem presentationHom_borel_le_source :
    (Presentation.roots.borel Presentation.relations).map b.presentationHom ≤ Q.tits.B := by
  rintro g ⟨x,hx,rfl⟩
  obtain ⟨v,p,rfl⟩ := (Presentation.roots.mem_borel_iff Presentation.relations x).mp hx
  rw [map_mul, b.presentationHom_product, b.presentationHom_torus]
  apply b.borel_le_source
  exact (b.signed.roots.mem_borel_iff b.relations _).mpr ⟨v,p,rfl⟩

/-- Every original representative is hit through the same quotient projection. -/
theorem original_presentation_preimage (x : X) :
    ∃ u : Presentation.Universal m hm, b.presentationHom u = Q.q x :=
  b.presentationHom_surjective (Q.q x)

/-- The same statement applies to each endpoint and every element of its whole overlap. -/
theorem marked_presentation_preimage {L D R : Type*} [Group L] [Group D] [Group R]
    {α : RankTwoAmalgam L D R} (e0 : RankTwoAmalgam.Iso α Q.standardAmalgam) (x : D) :
    ∃ u : Presentation.Universal m hm, b.presentationHom u = (e0.middle x).val :=
  b.presentationHom_surjective _

end BruhatRootData
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation

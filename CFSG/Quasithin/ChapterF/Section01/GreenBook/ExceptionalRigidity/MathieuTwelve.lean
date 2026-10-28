module

public import Theory.GroupTheory.Amalgam.SylowRigidity
public import Theory.GroupTheory.Amalgam.TwistTransport
public import Theory.Mathieu.M12.ExceptionalParabolics.EightExtensions
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12

/-!
# Faithful twist rigidity for M₁₂ and Aut(M₁₂)

For the inner model, faithfulness forces preservation of the first parabolic's
specific normal elementary eight. The proved eight-preserving extension
calculation extends each such automorphism to the first endpoint. For the
outer model, every overlap automorphism extends to the actual nonsplit first
endpoint. In both cases the right extension is the identity, so the overlap
factorization has l = d and r = 1.

The proofs below transport the extensions through both literal inclusion
squares, including the full Aut(M₁₂) carrier equivalence, and apply Sylow
normalization to arbitrary faithful input amalgams with parabolically
isomorphic endpoints. The final factorization and compatible-isomorphism
theorems have no additional endpoint-extension premises. The earlier
conditional interfaces are retained as separate reductions.

Source context: Aschbacher--Smith, F.1.11--12, printed pp.262--263. Those pages
distinguish parabolic equivalence from compatible amalgam isomorphism. The
separate source alignment with Goldschmidt and Fan remains with the parent
exceptional-rigidity assembly. Only the proved corrected outer core and the
literal model equivalences are used here.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterF.GreenBook.MathieuTwistRigidity
open Theory.GroupTheory RankTwoAmalgam
open Sporadic.Mathieu

/-- The inner calculation is extension of the stabilizer of a
specified subgroup, without any faithfulness or factorization premise. -/
def InnerEightExtensions : Prop :=
  ∀ d : MulAut M12SmallPair.sylowCandidate,
    M12SmallPair.ExceptionalParabolics.TwistObstruction.overlapEight.map d.toMonoidHom =
      M12SmallPair.ExceptionalParabolics.TwistObstruction.overlapEight →
    ExtendsAcross M12SmallPair.ExceptionalParabolics.amalgam.left d

/-- The outer calculation concerns the genuine nonsplit endpoint. -/
def OuterOverlapExtensions : Prop :=
  ∀ d : MulAut M12ExceptionalExtension.overlap,
    ExtendsAcross M12ExceptionalExtension.VerifiedPair.amalgam.left d

/-- The finite calculation on the marked inner carrier supplies the stabilizer extension. -/
theorem inner_eight_extensions : InnerEightExtensions :=
  M12SmallPair.ExceptionalParabolics.EightExtensions.extendsAcross_of_preserves_overlapEight

/-- The finite calculation on the genuine outer carrier supplies every extension. -/
theorem outer_overlap_extensions : OuterOverlapExtensions :=
  M12ExceptionalExtension.overlap_automorphisms_extend

/-- Faithfulness discharges the stabilizer condition; the right extension is identity. -/
theorem m12_factorsThrough_of_eight_extensions (hext : InnerEightExtensions) :
    ∀ d : MulAut MathieuTwelve.B,
      Faithful (twistRight MathieuTwelve.amalgam d) →
        FactorsThrough MathieuTwelve.amalgam d := by
  apply MathieuTwelve.concreteIso.symm.transport_faithful_factorization
  intro d hf
  exact FactorsThrough.of_left (hext d
    (M12SmallPair.ExceptionalParabolics.TwistObstruction.preserves_overlapEight_of_faithful d hf))

/-- Literal transport through the marked extension and its full automorphism equivalence. -/
theorem autM12_factorsThrough_of_overlap_extensions (hext : OuterOverlapExtensions) :
    ∀ d : MulAut AutMathieuTwelve.autB,
      Faithful (twistRight AutMathieuTwelve.autAmalgam d) →
        FactorsThrough AutMathieuTwelve.autAmalgam d := by
  apply (AutMathieuTwelve.concreteIso.symm.trans
    AutMathieuTwelve.ambientIso).transport_faithful_factorization
  intro d _
  exact FactorsThrough.of_left (hext d)

/-- A faithful twist extends to the literal first GreenBook M₁₂ endpoint. -/
theorem m12_extendsAcross_of_faithful (d : MulAut MathieuTwelve.B)
    (hf : Faithful (twistRight MathieuTwelve.amalgam d)) :
    ExtendsAcross MathieuTwelve.amalgam.left d := by
  let e := MathieuTwelve.concreteIso.symm
  obtain ⟨c, rfl⟩ := (MulAut.congr e.middle).surjective d
  have hc := (e.twistRightIso c).symm.faithful hf
  exact (inner_eight_extensions c
    (M12SmallPair.ExceptionalParabolics.TwistObstruction.preserves_overlapEight_of_faithful
      c hc)).transport e.middle e.left e.left_commutes

/-- Every overlap automorphism extends to the first endpoint inside literal Aut(M₁₂). -/
theorem autM12_extendsAcross (d : MulAut AutMathieuTwelve.autB) :
    ExtendsAcross AutMathieuTwelve.autAmalgam.left d := by
  let e := AutMathieuTwelve.concreteIso.symm.trans AutMathieuTwelve.ambientIso
  obtain ⟨c, rfl⟩ := (MulAut.congr e.middle).surjective d
  exact (outer_overlap_extensions c).transport e.middle e.left e.left_commutes

/-- Faithful M₁₂ twists factor with left restriction d and identity right extension. -/
theorem m12_factorsThrough (d : MulAut MathieuTwelve.B)
    (hf : Faithful (twistRight MathieuTwelve.amalgam d)) :
    FactorsThrough MathieuTwelve.amalgam d :=
  FactorsThrough.of_left (m12_extendsAcross_of_faithful d hf)

/-- Every outer twist factors with left restriction d and identity right extension. -/
theorem autM12_factorsThrough (d : MulAut AutMathieuTwelve.autB) :
    FactorsThrough AutMathieuTwelve.autAmalgam d :=
  FactorsThrough.of_left (autM12_extendsAcross d)

theorem m12_sylow : SylowEmbedded 2 MathieuTwelve.amalgam :=
  sylowEmbedded_ofSubgroups MathieuTwelve.S _ _ _ _ _ MathieuTwelve.B_eq_S

theorem autM12_sylow : SylowEmbedded 2 AutMathieuTwelve.autAmalgam := by
  apply sylowEmbedded_ofSubgroups AutMathieuTwelve.autS
  exact congrArg (Subgroup.map AutMathieuTwelve.ambientEquiv.toMonoidHom)
    AutMathieuTwelve.B_eq_S

variable {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R}

/-- Conditional arbitrary-input recognition, retaining both overlap squares. -/
theorem m12_iso_of_eight_extensions (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (e : ParabolicEquiv α MathieuTwelve.amalgam) (hext : InnerEightExtensions) :
    Nonempty (Iso α MathieuTwelve.amalgam) :=
  iso_of_faithful_twist_factorization hα m12_sylow hf e
    (m12_factorsThrough_of_eight_extensions hext)

/-- The arbitrary-input consumer lands inside the literal full automorphism group. -/
theorem autM12_iso_of_overlap_extensions (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (e : ParabolicEquiv α AutMathieuTwelve.autAmalgam) (hext : OuterOverlapExtensions) :
    Nonempty (Iso α AutMathieuTwelve.autAmalgam) :=
  iso_of_faithful_twist_factorization hα autM12_sylow hf e
    (autM12_factorsThrough_of_overlap_extensions hext)

/-- Any faithful Sylow amalgam parabolically equivalent to M₁₂ is compatibly
isomorphic to its literal GreenBook model, with both overlap squares. -/
theorem m12_iso (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (e : ParabolicEquiv α MathieuTwelve.amalgam) :
    Nonempty (Iso α MathieuTwelve.amalgam) :=
  iso_of_faithful_twist_factorization hα m12_sylow hf e m12_factorsThrough

/-- Arbitrary-input compatible recognition in the full Aut(M₁₂) carrier,
with no additional extension or factorization premise. -/
theorem autM12_iso (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (e : ParabolicEquiv α AutMathieuTwelve.autAmalgam) :
    Nonempty (Iso α AutMathieuTwelve.autAmalgam) :=
  iso_of_faithful_twist_factorization hα autM12_sylow hf e
    (fun d _ => autM12_factorsThrough d)

end CFSG.Quasithin.ChapterF.GreenBook.MathieuTwistRigidity

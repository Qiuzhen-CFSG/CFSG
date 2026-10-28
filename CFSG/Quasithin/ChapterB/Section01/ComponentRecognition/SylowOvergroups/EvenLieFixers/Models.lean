module

public import CFSG.KnownSimple.ClassicalModels
public import CFSG.KnownSimple.ExceptionalModels
public import Theory.SpecificGroups.Triality.StandardModel
public import Theory.SpecificGroups.ReeF4.Model
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import BenderSuzuki.MatrixGroups.Suzuki
public import Theory.SpecificGroups.Tits.Presentation

/-!
# The characteristic-two model input to B.1.13

Every alternative names a concrete carrier through an actual multiplicative
equivalence. These are the full characteristic-two families, with arbitrary
classical rank, the exceptional F/E families, triality and large Ree, and the
three characteristic-two small derived cases. Rank-one aliases retain their
usual exclusions. In particular the nonsimple full Sp₄(2) and G₂(2) are not
substituted for their derived groups, and the Tits endpoint is separate from
the large Ree range. The small Ree group has defining characteristic three
and is not an additional characteristic-two family.

This is only a recognition interface. It asserts neither recognition nor a
fixer bound; finiteness, simplicity and perfectness are inherited from the
component application. The remaining family calculations must all be proved
before this interface can supply the general B.1.13 fixer theorem.

Sources: Aschbacher–Smith, B.1.13, printed pp.73–74; GLS3, 2.2.7–2.2.8
and §2.7 (`refs/KGroup/GLS3/chapter2.tex`). Parameter ranges and carrier
conventions agree with `CFSG.KnownSimple.CarrierCatalogue`.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers

inductive LinearUnitaryModel (X : Type*) [Group X] : Prop
  | linear (d f : ℕ) (hf : 0 < f)
      (parameters : KnownSimple.LinearParameters d (2 ^ f))
      (model : ClassicalGroup.IsPSL X d (2 ^ f))
  | unitary (d f : ℕ) (hf : 0 < f)
      (parameters : KnownSimple.UnitaryParameters d (2 ^ f))
      (model : ClassicalGroup.IsPSU X d (2 ^ f))

inductive SymplecticOrthogonalModel (X : Type*) [Group X] : Prop
  | symplectic (r f : ℕ) (hf : 0 < f)
      (parameters : KnownSimple.SymplecticParameters r (2 ^ f))
      (model : ClassicalGroup.IsPSp X r (2 ^ f))
  | orthogonalPlus (r f : ℕ) (hf : 0 < f)
      (parameters : KnownSimple.OrthogonalPlusParameters r (2 ^ f))
      (model : ClassicalGroup.IsPOmegaPlus X r (2 ^ f))
  | orthogonalOdd (r f : ℕ) (hf : 0 < f)
      (parameters : KnownSimple.OrthogonalOddParameters r (2 ^ f))
      (model : ClassicalGroup.IsPOmegaOdd X r (2 ^ f))
  | orthogonalMinus (r f : ℕ) (hf : 0 < f)
      (parameters : KnownSimple.OrthogonalMinusParameters r (2 ^ f))
      (model : ClassicalGroup.IsPOmegaMinus X r (2 ^ f))
  | symplecticDerived
      (iso : Nonempty (X ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))

inductive ExceptionalModel (X : Type*) [Group X] : Prop
  | f4 (f : ℕ) (hf : 0 < f) (model : ExceptionalGroup.IsF4 X (2 ^ f))
  | e6 (f : ℕ) (hf : 0 < f) (model : ExceptionalGroup.IsE6 X (2 ^ f))
  | e7 (f : ℕ) (hf : 0 < f) (model : ExceptionalGroup.IsE7 X (2 ^ f))
  | e8 (f : ℕ) (hf : 0 < f) (model : ExceptionalGroup.IsE8 X (2 ^ f))
  | twistedE6 (f : ℕ) (hf : 0 < f)
      (model : ExceptionalGroup.IsTwistedE6 X (2 ^ f))

/-- The full source family input, with genuine model isomorphisms in every branch. -/
inductive Model (X : Type*) [Group X] : Prop
  | linearUnitary (model : LinearUnitaryModel X)
  | symplecticOrthogonal (model : SymplecticOrthogonalModel X)
  | exceptional (model : ExceptionalModel X)
  | g2 (F : Type) [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
      (iso : Nonempty (X ≃* Atlas.G2.Model F))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | triality (f : ℕ) (hf : 0 < f)
      (model : Triality.Standard.IsTrialityGroupAt (2 ^ f) X)
  | ree (model : ReeF4.IsReeF4Model X)
  | g2Derived (iso : Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | tits (iso : Nonempty (X ≃* Tits.ParrottGroup))

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers

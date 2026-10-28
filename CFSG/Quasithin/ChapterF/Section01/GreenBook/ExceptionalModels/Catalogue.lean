module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.SourceMarkings
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko.Assembly
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12

/-!
# The verified exceptional catalogue for F.1.12

Each catalogue entry is tied to a fixed concrete inclusion amalgam. The raw
`ParabolicModel` relation identifies its three groups. The `IsModel` relation
requires both commuting squares except in the two Hall--Janko cases, exactly
as in F.1.11--12. Neither relation asserts recognition or uniqueness.

`local_assertions` assembles the proved local calculations for all six
exceptional alternatives and the two binary automorphism extensions. It has
no model-construction or local-structure premises. The Tits row uses the
proved correction (first core 512 and quotient Sz(2)); the outer M₁₂ row
uses the marked wreath quotient and residual quaternion central product.
The separate recognition and rigidity proofs must produce `IsModel` from
the source hypotheses; the calculations here do not assert that converse.

Source: Aschbacher--Smith F.1.12(I)(8)--(13), and q=2 in (3), (5), printed
pp.262--264; E.2.16, p.228; 14.2.21, pp.988--989. For the Tits correction
see Parrott (1972), p.672 and `Tits.ExceptionalParabolics.SourceCorrection`.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterF.GreenBook.ExceptionalModels
open Theory.GroupTheory
open scoped MatrixGroups

/-- The six exceptional alternatives and the two extensions used in their proof. -/
inductive Case where
  | g2Derived | tits | j2 | autJ2 | m12 | autM12 | g2Full | reeFull

variable {L B R : Type*} [Group L] [Group B] [Group R]

/-- Local equivalence to a fixed constructed model, for the raw-recognition and
rigidity interfaces. No compatibility or uniqueness is asserted here. -/
def ParabolicModel (c : Case) (α : RankTwoAmalgam L B R) : Prop :=
  match c with
  | .g2Derived => Nonempty (RankTwoAmalgam.ParabolicEquiv α G2.simpleAmalgam)
  | .tits => Nonempty (RankTwoAmalgam.ParabolicEquiv α Tits.ExceptionalParabolics.amalgam)
  | .j2 => Nonempty (RankTwoAmalgam.ParabolicEquiv α HallJanko.j2Model.toMarking.amalgam)
  | .autJ2 => Nonempty (RankTwoAmalgam.ParabolicEquiv α HallJanko.autJ2Model.toMarking.amalgam)
  | .m12 => Nonempty (RankTwoAmalgam.ParabolicEquiv α MathieuTwelve.amalgam)
  | .autM12 => Nonempty (RankTwoAmalgam.ParabolicEquiv α AutMathieuTwelve.autAmalgam)
  | .g2Full => Nonempty (RankTwoAmalgam.ParabolicEquiv α G2.fullAmalgam)
  | .reeFull => Nonempty (RankTwoAmalgam.ParabolicEquiv α Tits.ExceptionalParabolics.FullRee.amalgam)

/-- The precise equivalence relation in the source conclusion: only J₂ and
Aut(J₂) stop at parabolic equivalence. Every other case retains both squares. -/
def IsModel (c : Case) (α : RankTwoAmalgam L B R) : Prop :=
  match c with
  | .g2Derived => G2.IsDerivedAmalgam α
  | .tits => IsAtlasTitsAmalgam α
  | .j2 => ParabolicModel .j2 α
  | .autJ2 => ParabolicModel .autJ2 α
  | .m12 => MathieuTwelve.IsM12Amalgam α
  | .autM12 => AutMathieuTwelve.IsAutM12Amalgam α
  | .g2Full => G2.IsFullAmalgam α
  | .reeFull => IsBinaryReeAmalgam α

/-- Forgetting commuting squares never changes the fixed model. The converse
is deliberately left to the separate exceptional-rigidity theorem. -/
theorem IsModel.parabolic {c : Case} {α : RankTwoAmalgam L B R}
    (h : IsModel c α) : ParabolicModel c α := by
  cases c with
  | j2 | autJ2 => exact h
  | g2Derived | tits | m12 | autM12 | g2Full | reeFull =>
    obtain ⟨e⟩ := h
    exact ⟨e.toParabolicEquiv⟩

/-- The fixed J₂ entry supplies the existing carrier-indexed source predicate. -/
theorem IsModel.j2_source {α : RankTwoAmalgam L B R} (h : IsModel .j2 α) :
    HallJanko.IsJ2ParabolicModel α := ⟨HallJanko.j2Model, h⟩

/-- The outer entry likewise refers to the full automorphism group of that carrier. -/
theorem IsModel.autJ2_source {α : RankTwoAmalgam L B R} (h : IsModel .autJ2 α) :
    HallJanko.IsAutJ2ParabolicModel α := ⟨HallJanko.autJ2Model, h⟩

/-- All local assertions on the literal constructed factors. The first G₂ core
uses L₁S, the outer J₂ quotient uses L₁S, and the outer M₁₂ denominator is
the original marked central omega subgroup. The Tits row records the corrected
quotient and core, with the original group alternative unchanged. -/
def LocalAssertions : Case → Prop
  | .g2Derived =>
    Nonempty ((G2.derivedL₁ ⧸ pCore 2 G2.derivedL₁) ≃* PSL(2, ZMod 2)) ∧
    Nonempty ((G2.derivedL₂ ⧸ pCore 2 G2.derivedL₂) ≃* PSL(2, ZMod 2)) ∧
    Nonempty (pCore 2 (G2.derivedL₁ ⊔ (G2.derivedS : Subgroup G2.Derived) :
      Subgroup G2.Derived) ≃* QuaternionCyclic.Model) ∧
    Nonempty (pCore 2 (G2.derivedL₂ ⊔ (G2.derivedS : Subgroup G2.Derived) :
      Subgroup G2.Derived) ≃* Atlas.G2.ExceptionalLocalQuotients.C4Square)
  | .tits =>
    Nonempty ((Tits.ExceptionalParabolics.firstLocalFactor ⧸
      pCore 2 Tits.ExceptionalParabolics.firstLocalFactor) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∧
    Nat.card (pCore 2 Tits.ExceptionalParabolics.firstLocalFactor) = 512 ∧
    Nonempty ((Tits.ExceptionalParabolics.secondLocalFactor ⧸
      pCore 2 Tits.ExceptionalParabolics.secondLocalFactor) ≃*
        ReeF4.LargeLocalSeeds.LinearQuotient 0) ∧
    Nat.card (pCore 2 Tits.ExceptionalParabolics.secondLocalFactor) = 1024
  | .j2 =>
    ClassicalGroup.IsPSL (HallJanko.j2Model.L 0 ⧸ pCore 2 (HallJanko.j2Model.L 0)) 2 4 ∧
    Sporadic.LeechRelated.J2.IsQuaternionDihedralCore (pCore 2 (HallJanko.j2Model.L 0)) ∧
    ClassicalGroup.IsPSL (HallJanko.j2Model.L 1 ⧸ pCore 2 (HallJanko.j2Model.L 1)) 2 2 ∧
    Nat.card (pCore 2 (HallJanko.j2Model.L 1)) = 64
  | .autJ2 =>
    Nonempty ((HallJanko.autJ2Model.toMarking.LS 0 ⧸
      pCore 2 (HallJanko.autJ2Model.toMarking.LS 0)) ≃* Equiv.Perm (Fin 5)) ∧
    Sporadic.LeechRelated.J2.IsQuaternionDihedralCore (pCore 2 (HallJanko.autJ2Model.L 0)) ∧
    Nonempty ((HallJanko.autJ2Model.L 1 ⧸ pCore 2 (HallJanko.autJ2Model.L 1)) ≃*
      Equiv.Perm (Fin 3)) ∧
    Nat.card (pCore 2 (HallJanko.autJ2Model.L 1)) = 64
  | .m12 =>
    ClassicalGroup.IsPSL (MathieuTwelve.L 0 ⧸ pCore 2 (MathieuTwelve.L 0)) 2 2 ∧
    Nonempty (Subgroup.QuaternionCentralProductData (pCore 2 (MathieuTwelve.L 0))) ∧
    ClassicalGroup.IsPSL (MathieuTwelve.L 1 ⧸ pCore 2 (MathieuTwelve.L 1)) 2 2 ∧
    Nat.card (pCore 2 (MathieuTwelve.L 1)) = 32
  | .autM12 =>
    ClassicalGroup.IsPSL (AutMathieuTwelve.L 0 ⧸ pCore 2 (AutMathieuTwelve.L 0)) 2 2 ∧
    Nat.card (pCore 2 (AutMathieuTwelve.L 0)) = 64 ∧
    Nonempty (Subgroup.QuaternionCentralProductData
      (⁅pCore 2 (AutMathieuTwelve.L 0), pResidual 2 (AutMathieuTwelve.L 0)⁆ :
        Subgroup (AutMathieuTwelve.L 0))) ∧
    Nonempty ((pCore 2 (AutMathieuTwelve.L 0)) ⧸
      Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic.intrinsicDistinguished ≃*
        QuaternionSwapModel.W) ∧
    ClassicalGroup.IsPSL (AutMathieuTwelve.L 1 ⧸ pCore 2 (AutMathieuTwelve.L 1)) 2 2 ∧
    Nat.card (pCore 2 (AutMathieuTwelve.L 1)) = 64
  | .g2Full =>
    Nonempty ((G2.fullL₁ ⧸ pCore 2 G2.fullL₁) ≃* PSL(2, ZMod 2)) ∧
    Nonempty ((G2.fullL₂ ⧸ pCore 2 G2.fullL₂) ≃* PSL(2, ZMod 2)) ∧
    (let Q := pCore 2 (G2.fullL₁ ⊔ (G2.fullS : Subgroup G2.Full) : Subgroup G2.Full)
     IsPGroup 2 Q ∧ commutator Q ≠ ⊥ ∧ commutator Q = Subgroup.center Q ∧
       frattini Q = Subgroup.center Q ∧ IsElementaryAbelian 2 (Subgroup.center Q) ∧
       Nat.card Q = 32 ∧ Nat.card (Subgroup.center Q) = 2) ∧
    Nat.card (pCore 2 (G2.fullL₂ ⊔ (G2.fullS : Subgroup G2.Full) : Subgroup G2.Full)) = 32
  | .reeFull =>
    Nonempty ((Tits.ExceptionalParabolics.FullRee.first ⧸
      pCore 2 Tits.ExceptionalParabolics.FullRee.first) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∧
    Nat.card (pCore 2 Tits.ExceptionalParabolics.FullRee.first) = 1024 ∧
    Nonempty ((Tits.ExceptionalParabolics.FullRee.second ⧸
      pCore 2 Tits.ExceptionalParabolics.FullRee.second) ≃*
        ReeF4.LargeLocalSeeds.LinearQuotient 0) ∧
    Nat.card (pCore 2 Tits.ExceptionalParabolics.FullRee.second) = 2048

/-- All eight concrete rows are proved, without any additional local premise.
This assembles the model calculations, not the recognition of an arbitrary amalgam. -/
theorem local_assertions (c : Case) : LocalAssertions c := by
  cases c with
  | g2Derived =>
    exact ⟨⟨Atlas.G2.ExceptionalLocalQuotients.derivedFirstQuotientEquiv⟩,
      ⟨Atlas.G2.ExceptionalLocalQuotients.derivedSecondQuotientEquiv⟩,
      ⟨G2.derivedFirstSylowCoreEquiv⟩, ⟨G2.derivedSecondSylowCoreEquiv⟩⟩
  | tits =>
    exact ⟨⟨Tits.ExceptionalParabolics.firstLocalFactorCoreQuotientEquiv⟩,
      Tits.ExceptionalParabolics.localFactor_core_cards.1,
      ⟨Tits.ExceptionalParabolics.secondLocalFactorCoreQuotientEquiv⟩,
      Tits.ExceptionalParabolics.localFactor_core_cards.2⟩
  | j2 =>
    exact ⟨HallJanko.j2Model.L₁_quotient, HallJanko.j2Model.L₁_core,
      HallJanko.j2Model.L₂_quotient, HallJanko.j2Model.L₂_core_card⟩
  | autJ2 =>
    exact ⟨HallJanko.autJ2Model.L₁S_quotient, HallJanko.autJ2Model.L₁_core,
      HallJanko.autJ2Model.L₂_quotient, HallJanko.autJ2Model.L₂_core_card⟩
  | m12 => exact MathieuTwelve.local_calculations
  | autM12 => exact AutMathieuTwelve.local_calculations
  | g2Full => exact G2.source_I_3.2
  | reeFull =>
    exact ⟨⟨Tits.ExceptionalParabolics.FullRee.firstCoreQuotientEquiv⟩,
      Tits.ExceptionalParabolics.FullRee.first_core_card,
      ⟨Tits.ExceptionalParabolics.FullRee.secondCoreQuotientEquiv⟩,
      Tits.ExceptionalParabolics.FullRee.second_core_card⟩

/-- The four extensions in F.1.12's proof are identified with the full
actual automorphism groups. Their marked amalgam transports are exported
by the individual model modules. -/
theorem automorphism_extensions :
    Nonempty (G2.Full ≃* MulAut G2.Derived) ∧
    Nonempty (ReeF4.Model 0 ≃* MulAut Tits.Atlas1600Group) ∧
    Nonempty (Sporadic.LeechRelated.J2.ExceptionalParabolics.Extension ≃*
      MulAut Sporadic.LeechRelated.J2.Carrier) ∧
    Nonempty (Sporadic.Mathieu.M12ExceptionalExtension.Carrier ≃*
      MulAut Sporadic.Mathieu.M12) :=
  ⟨⟨G2.automorphismEquiv⟩, ⟨Tits.ExceptionalParabolics.FullRee.atlasAutEquiv⟩,
    ⟨Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionEquivAut⟩,
    ⟨AutMathieuTwelve.ambientEquiv⟩⟩

end CFSG.Quasithin.ChapterF.GreenBook.ExceptionalModels

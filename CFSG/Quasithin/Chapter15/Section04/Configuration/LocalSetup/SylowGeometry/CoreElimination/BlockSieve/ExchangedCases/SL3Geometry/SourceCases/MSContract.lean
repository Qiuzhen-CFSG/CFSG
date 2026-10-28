module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
public import Theory.SpecificGroups.Triality.StandardModel
public import Theory.SpecificGroups.ReeF4.Model

/-!
# The complete MS-pair input for the SL₃ application

This fallback contract records C.1.31 literally. Its rank-two clause uses
actual derived subgroups of the concrete characteristic-two groups, including
all small derived endpoints. Both alternatives in MS2 are retained; the G₂(2)
parabolics are conjugates of its two root-defined standard parabolics.
These are definitions, not assertions of the MS classification.

Source: Aschbacher–Smith, C.1.31–34, printed pp.135–137.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u

/-- All characteristic-two Lie-rank-two derived groups in MS1. The unitary
field is the matrix field, of order q². No SQTK restriction is used to delete
families from this input. The small Sp₄(2), G₂(2), and ²F₄(2) derived groups
are included by taking the actual commutator subgroups. -/
inductive RankTwoDerived (A : Type u) [Group A] : Prop
  | linear (T : Type) [Group T] (n : ℕ) (hn : 0 < n)
      (model : ClassicalGroup.IsPSL T 3 (2 ^ n))
      (iso : Nonempty (A ≃* commutator T))
  | symplectic (T : Type) [Group T] (n : ℕ) (hn : 0 < n)
      (model : ClassicalGroup.IsPSp T 2 (2 ^ n))
      (iso : Nonempty (A ≃* commutator T))
  | unitaryFour (T : Type) [Group T] (n : ℕ) (hn : 0 < n)
      (model : ClassicalGroup.IsPSU T 4 (2 ^ n))
      (iso : Nonempty (A ≃* commutator T))
  | unitaryFive (T : Type) [Group T] (n : ℕ) (hn : 0 < n)
      (model : ClassicalGroup.IsPSU T 5 (2 ^ n))
      (iso : Nonempty (A ≃* commutator T))
  | g2 (F : Type) [Field F] [Finite F] (n : ℕ) (hn : 0 < n)
      (hF : Nat.card F = 2 ^ n)
      (iso : Nonempty (A ≃* commutator (Atlas.G2.Model F)))
  | triality (T : Type) [Group T] (n : ℕ) (hn : 0 < n)
      (model : Triality.Standard.IsTrialityGroupAt (2 ^ n) T)
      (iso : Nonempty (A ≃* commutator T))
  | ree (m : ℕ) (iso : Nonempty (A ≃* commutator (ReeF4.Model m)))

/-- The two conjugacy classes of actual maximal parabolics of G₂(2). -/
def G2MaximalParabolic (P : Subgroup (Atlas.G2.Model (ZMod 2))) : Prop :=
  ∃ g : Atlas.G2.Model (ZMod 2),
    P = (Atlas.G2.LieParabolicSetup.parabolic₁ (F := ZMod 2)).map (MulAut.conj g).toMonoidHom ∨
    P = (Atlas.G2.LieParabolicSetup.parabolic₂ (F := ZMod 2)).map (MulAut.conj g).toMonoidHom

/-- Exactly MS2(b): intrinsic containment and normality in a maximal
parabolic of the actual quotient, together with its elementary order eight. -/
def MSExceptionalRadical {G : Type u} [Group G] (R : Subgroup G) : Prop :=
  ∃ e : (G ⧸ pCore 2 G) ≃* Atlas.G2.Model (ZMod 2),
    pCore 2 G ≤ R ∧
    ∃ P : Subgroup (G ⧸ pCore 2 G),
      G2MaximalParabolic (P.map e.toMonoidHom) ∧
      R.map (QuotientGroup.mk' (pCore 2 G)) ≤ P ∧
      ((R.map (QuotientGroup.mk' (pCore 2 G))).subgroupOf P).Normal ∧
      IsElementaryAbelian 2 (R.map (QuotientGroup.mk' (pCore 2 G))) ∧
      Nat.card (R.map (QuotientGroup.mk' (pCore 2 G))) = 8

/-- The complete C.1.31 input. The product is literal setwise multiplication;
normality is always relative to the displayed ambient group. -/
structure MSPair (κ : GroupClass.{u}) (G : Type u) [Group G]
    (L R : Subgroup G) : Prop where
  finite : Finite G
  sqtk : IsSQTK κ G
  fitting : generalizedFitting G = pCore 2 G
  product : ∀ g : G, ∃ l ∈ L, ∃ r ∈ R, l * r = g
  component : L.IsCComponent
  rankTwo : RankTwoDerived (L ⧸ centralPreimage (pCore 2 L))
  radical_alternatives : ChapterC.MSOddIndexRadical R ∨ MSExceptionalRadical R
  characteristic : ChapterC.MSCharacteristicCondition R

/-- C.1.31 defines an MS-group existentially. -/
def IsMSGroup (κ : GroupClass.{u}) (G : Type u) [Group G] : Prop :=
  ∃ L R : Subgroup G, MSPair κ G L R

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

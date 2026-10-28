module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.LocalGeometry
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry

/-!
# Ordinary conclusions of original 15.1.20 and 15.1.22

These are conclusion interfaces for the independent source arguments, not
classification theorems. The initial catalogue retains the Bender and
higher-field rows for the separate 15.1.21 argument. The final catalogue
retains both actual parabolics, centralizers, and the embedded residuals.

All models are multiplicative equivalences. A parabolic over the given
Sylow contains its normalizer (the Borel in the recognized Lie models).
Binary linear parabolics additionally use actual flag stabilizers under
one fixed model equivalence. Sporadic rows concern L/Z(L); the binary
rank-two, M11 and binary linear rows concern L itself.
Source: Aschbacher--Smith, printed pp.1094--1100.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 ClassificationModels
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The Borel over the literal S_L, embedded back into G. -/
def ordinaryBorel (d : CaseIComponentData T M Mc V) : Subgroup G :=
  (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype

/-- A proper parabolic over S_L in a recognized group of Lie type. -/
def OrdinaryParabolic (d : CaseIComponentData T M Mc V) (P : Subgroup G) : Prop :=
  P < d.L ∧ d.ordinaryBorel ≤ P

/-- The three actual binary rank-two simple groups in 15.1.20(3c). -/
def OrdinaryBinaryRankTwo (K : Type*) [Group K] : Prop :=
  Nonempty (K ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
    Nonempty (K ≃* Tits.ParrottGroup) ∨
    Nonempty (K ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one)

/-- The higher-field linear/symplectic possibilities, including the
central two-covers of L3(4). The last clause identifies the actual quotient. -/
def OrdinaryHigherField (d : CaseIComponentData T M Mc V) : Prop :=
  (∃ n : ℕ, 1 < n ∧
    (ClassicalGroup.IsPSL d.L 3 (2 ^ n) ∨ ClassicalGroup.IsPSp d.L 2 (2 ^ n))) ∨
      ClassicalGroup.IsPSL (d.L ⧸ pCore 2 d.L) 3 4

/-- A flag parabolic under the same actual binary linear isomorphism. -/
def OrdinaryLinearParabolic (d : CaseIComponentData T M Mc V) {n : ℕ}
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (P : Subgroup G) : Prop :=
  P < d.L ∧ ∃ k : ℕ, 0 < k ∧ ∃ f : LinearFlag (ZMod 2) n k,
    (P.subgroupOf d.L).map e.toMonoidHom = f.stabilizer

/-- The exact centralizer identity in ordinary rows (4), (5), and (7). -/
def OrdinaryCentralizerIdentity (d : CaseIComponentData T M Mc V) : Prop :=
  d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
    (M ⊓ d.L).subtype) : Set G) = d.S ⊓ centralizer (d.L : Set G)

/-- The five conclusions of 15.1.20(3), before any rank-one exclusion. -/
inductive Ordinary20Alternatives (d : CaseIComponentData T M Mc V) : Prop
  | rankOne
      (model : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
      (borel : d.ML = d.ordinaryBorel)
  | higherField (model : d.OrdinaryHigherField)
      (parabolic : d.OrdinaryParabolic d.ML)
      (borel_or_maximal : d.ML = d.ordinaryBorel ∨ IsCoatom (d.ML.subgroupOf d.L))
  | binaryRankTwo (model : OrdinaryBinaryRankTwo d.L)
      (centralizing : d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G))
  | sporadic (name : SporadicName) (not_j3 : name ≠ .j3) (not_j4 : name ≠ .j4)
      (model : Nonempty ((d.L ⧸ pCore 2 d.L) ≃* name.Carrier))
      (centralizing : d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G))
  | linear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (equiv : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
      (parabolic : d.OrdinaryLinearParabolic equiv d.ML)
      (centralizer_le : d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML)

/-- All four ordinary conclusions of 15.1.22, with the residual in the
M11 row taken inside the literal G₁-normalizer of J(S). -/
inductive Ordinary22Alternatives (d : CaseIComponentData T M Mc V) : Prop
  | binaryRankTwo (model : OrdinaryBinaryRankTwo d.L)
      (centralizing : d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G))
      (marked_parabolic : d.OrdinaryParabolic d.ML)
      (selected_parabolic : d.OrdinaryParabolic (M ⊓ d.L))
      (marked_maximal : IsCoatom (d.ML.subgroupOf d.L))
      (selected_maximal : IsCoatom ((M ⊓ d.L).subgroupOf d.L))
      (distinct : d.ML ≠ M ⊓ d.L)
      (centralizers : d.OrdinaryCentralizerIdentity)
  | sporadic (name : SporadicName)
      (allowed : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨
        name = .j2 ∨ name = .he)
      (model : Nonempty ((d.L ⧸ center d.L) ≃* name.Carrier))
      (centralizing : d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G))
      (centralizers : d.OrdinaryCentralizerIdentity)
  | mathieuEleven (model : Nonempty (d.L ≃* Sporadic.Mathieu.M11))
      (centralizing : d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G))
      (thompson_residual :
        (pResidual 2 (normalizer
          ((elementaryAbelianMaxJ d.S).subgroupOf d.G1 : Set d.G1))).map
          (d.G1.subtype.comp (normalizer
            ((elementaryAbelianMaxJ d.S).subgroupOf d.G1 : Set d.G1)).subtype) ≤
              centralizer (d.L : Set G))
  | linear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (equiv : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
      (marked_parabolic : d.OrdinaryLinearParabolic equiv d.ML)
      (selected_parabolic : d.OrdinaryLinearParabolic equiv (M ⊓ d.L))
      (centralizer_le : d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML)
      (generated : d.ML ⊔ (M ⊓ d.L) = d.L)
      (centralizers : d.OrdinaryCentralizerIdentity)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

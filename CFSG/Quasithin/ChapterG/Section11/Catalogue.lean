module

public import CFSG.Quasithin.ChapterG.Section11.SmallCases
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.TensorModels
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.AlternatingSixTensor.Model
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.TwistedTensor.Rank
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.GTwo.LongRoot
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension.Matrix

/-!
# The thirteen output alternatives of G.11.2

These predicates describe the original group, representation, form and actor.
They are conclusions to be constructed, never premises of a classifier.
The two small alternatives are defined in `SmallCases`; the remaining ones
retain the concrete carriers, restricted actions, field sizes, split quadratic
form and the marked elements in cases (7), (8), (10) and (12).

The source only prescribes the group and dimension in (3) and (13); no extra
choice of module is imposed in those rows. In (8) and (12) the decompositions
are literal subspaces of V. In (11) the intertwiner is over F₈ after extension
of the original F₂ action. The G.9 whole-group tensor convention is not used.

Source: Aschbacher--Smith G.11.2, printed p.364 (PDF p.375).
Concrete model identifications are in the imported, attributed modules.
-/

@[expose] public section
open Subgroup Module Representation Theory.GroupTheory
open Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups TensorProduct
namespace CFSG.Quasithin.ChapterG.Section11
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- G.11.2(3), with both ends of the printed extension interval. -/
def CaseThree (_ρ : Representation (ZMod 2) G V) : Prop :=
  finrank (ZMod 2) V = 6 ∧
    ∃ H : Subgroup RankTwo.ExtraspecialModel.Model,
      RankTwo.ExtraspecialModel.fourExtension ≤ H ∧ Nonempty (G ≃* H)

/-- G.11.2(4): the natural A₇ action is the action of F*(G). -/
def CaseFour (ρ : Representation (ZMod 2) G V) : Prop :=
  finrank (ZMod 2) V = 6 ∧
    Section09.Quasiequivalent (ρ.comp (generalizedFitting G).subtype)
      (BinaryPermutation.alternatingCoreRepresentation (Fin 7))

/-- G.11.2(5). Coordinates in the hyperbolic three-plane sum specify Witt
index three; the polar form is exactly the supplied symplectic form. -/
def CaseFive (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) : Prop :=
  finrank (ZMod 2) V = 6 ∧
    ∃ q : QuadraticForm (ZMod 2) V, q.polarBilin = B ∧
    ∃ f : V ≃ₗ[ZMod 2] ClassicalOrthogonal.VectorD 3 (ZMod 2),
      (∀ w, q w = ClassicalOrthogonal.formD 3 (ZMod 2) (f w)) ∧
      ∃ H : Subgroup (Theory.AlgebraicGroup.quadraticIsometrySubgroup
          (ClassicalOrthogonal.formD 3 (ZMod 2))), H.index ≤ 2 ∧
        ∃ e : G ≃* H, ∀ g w, f (ρ g w) = (e g).val.val (f w)

/-- G.11.2(6) uses the full G₂(2), not only its derived subgroup. -/
def CaseSix (ρ : Representation (ZMod 2) G V) : Prop :=
  finrank (ZMod 2) V = 6 ∧
    Section09.Quasiequivalent ρ (Atlas.G2.Natural.action (ZMod 2))

/-- G.11.2(7), on the actual orthogonal module over the field of order four.
In characteristic two the projective elementary carrier is Ω₄⁺(4); the
imported `FourPlusMatrix.projectiveEquiv` identifies its two SL₂ factors. -/
def CaseSeven (ρ : Representation (ZMod 2) G V) (X : Subgroup G) : Prop :=
  finrank (ZMod 2) V = 8 ∧ ¬ X ≤ generalizedFitting G ∧
    Section09.Quasiequivalent (ρ.comp (generalizedFitting G).subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (ClassicalOrthogonal.projectiveElementaryNatural
          (ClassicalOrthogonal.formD 2 ClassicalOrthogonal.FourPlusMatrix.Binary.F)))

/-- G.11.2(8), retaining the isotropic E(G)-submodule and its actor-conjugate
complement. These are the actual subspaces of the original representation. -/
def CaseEight (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (X : Subgroup G) : Prop :=
  finrank (ZMod 2) V = 8 ∧ Nonempty (G ≃* Equiv.Perm (Fin 7)) ∧
    ∃ I : Submodule (ZMod 2) V, finrank (ZMod 2) I = 4 ∧
      (∀ u ∈ I, ∀ w ∈ I, B u w = 0) ∧
      componentLayer G ≤ subspaceStabilizer ρ I ∧
      ∃ x ∈ X, x ∉ subspaceStabilizer ρ I ∧ IsCompl I (I.map (ρ x))

/-- G.11.2(9), retaining both inequivalent four-dimensional A₅ modules and
both the S₅ and A₅ product options, with genuine tensor intertwiners. -/
def CaseNine (ρ : Representation (ZMod 2) G V) : Prop :=
  finrank (ZMod 2) V = 8 ∧
    (Section09.Quasiequivalent ρ RankTwo.TensorModels.orthogonalTensor ∨
     Section09.Quasiequivalent ρ RankTwo.TensorModels.orthogonalAlternatingTensor ∨
     Section09.Quasiequivalent ρ RankTwo.TensorModels.naturalTensor ∨
     Section09.Quasiequivalent ρ RankTwo.TensorModels.naturalBaseTensor)

/-- G.11.2(10). The equal-sign subgroup is the simultaneous transposition/
inversion extension of A₆ × C₃. The actual layer, three-core, distinguished
actor and tensor representation are all identified by the same coordinates. -/
def CaseTen (ρ : Representation (ZMod 2) G V) (X : Subgroup G) : Prop :=
  let M := RankTwo.Imprimitive.AlternatingSixTensor.GroupModel
  let base := RankTwo.Imprimitive.AlternatingSixTensor.base
  finrank (ZMod 2) V = 8 ∧
    ∃ e : G ≃* M,
      (componentLayer G).map e.toMonoidHom =
        (base.comp (MonoidHom.inl _ _)).range ∧
      (pCore 3 G).map e.toMonoidHom =
        (base.comp (MonoidHom.inr _ _)).range ∧
      (∃ f : V ≃ₗ[ZMod 2] RankTwo.Imprimitive.AlternatingSixTensor.TensorSpace,
        ∀ g w, f (ρ g w) = RankTwo.Imprimitive.AlternatingSixTensor.representation
          (e g) (f w)) ∧
      ∃ x ∈ X, (e x).val.1.IsSwap ∧ (e x).val.2.IsSwap ∧
        (∀ c ∈ pCore 3 G, x * c * x⁻¹ = c⁻¹) ∧
        zpowers x ⊔ (componentLayer G ⊔ pCore 3 G) = ⊤

/-- G.11.2(11). The field is F₈ and σ generates its full automorphism group.
The source's scalar extension is identified with the literal triple tensor. -/
def CaseEleven (ρ : Representation (ZMod 2) G V) : Prop :=
  let F := GaloisField 2 3
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  finrank (ZMod 2) V = 8 ∧
    ∃ e : generalizedFitting G ≃* Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ σ : F ≃+* F, zpowers σ = ⊤ ∧ orderOf σ = 3 ∧
        Nonempty ((Representation.extendScalars F
          ((ρ.comp (generalizedFitting G).subtype).comp e.symm.toMonoidHom)).Equiv
            (RankTwo.TwistedTensor.twistedTriple σ))

/-- G.11.2(12), with the original component, its x-conjugate, the moved
summands, the orthogonal A₅ module, and the exact elementary actor of order 8.
The chosen A₅ module is the orthogonal one, not the natural F₄-column action. -/
def CaseTwelve (ρ : Representation (ZMod 2) G V) (X : Subgroup G) : Prop :=
  finrank (ZMod 2) V = 8 ∧
    ∃ L : Subgroup G, IsComponent G L ∧
    ∃ x ∈ X, let Lx := L.map (MulAut.conj x).toMonoidHom
      generalizedFitting G = L ⊔ Lx ∧
      IsCompl (subspaceCommutator ρ ⊤ L) (subspaceCommutator ρ ⊤ Lx) ∧
      (∃ e : L ≃* alternatingGroup (Fin 5),
        ∃ f : (subspaceCommutator ρ ⊤ L) ≃ₗ[ZMod 2]
          RankTwo.Imprimitive.OrthogonalA5.Space,
          ∀ (l : L) w, ρ l (f.symm w : V) =
            (f.symm (RankTwo.Imprimitive.OrthogonalA5.representation (e l) w) : V)) ∧
      X = zpowers x ⊔ (X ⊓ (L ⊔ Lx)) ∧ Nat.card X = 8

/-- G.11.2(13), with the genuine nonsplit triple cover and its outer extension.
The source prescribes the dimension and group, with no further module clause. -/
def CaseThirteen (_ρ : Representation (ZMod 2) G V) : Prop :=
  finrank (ZMod 2) V = 12 ∧ Nonempty
    (G ≃* Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.actionGroup)

/-- The complete printed output list. Its exhaustive recognition is a separate
proof obligation; this definition supplies no inhabitant. -/
def Conclusion (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (X : Subgroup G) : Prop :=
  CaseOne ρ ∨ CaseTwo ρ B ∨ CaseThree ρ ∨ CaseFour ρ ∨ CaseFive ρ B ∨
    CaseSix ρ ∨ CaseSeven ρ X ∨ CaseEight ρ B X ∨ CaseNine ρ ∨ CaseTen ρ X ∨
    CaseEleven ρ ∨ CaseTwelve ρ X ∨ CaseThirteen ρ

end CFSG.Quasithin.ChapterG.Section11

module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement.Transport
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.Representation.OrthogonalNatural

/-!
# Marked outputs of the general-exponent refinement

The factor alternative identifies both literal central quotients
[U,Kᵢ]/C_[U,Kᵢ](Kᵢ) with one concrete natural, A₅, or even-exponent
Hermitian action. The second identification is transported by the actual
moving element, including its actor map. Directness is retained only
in the image modulo C_U(K₀).

The orthogonal alternative identifies U itself with the binary natural
action of the actual split projective orthogonal carrier. In characteristic
two the checked projectivization equivalence preserves that action. The
same group identification marks both factors of the supplied product.
The repository names this carrier ClassicalOrthogonal.POmegaPlus.

These are conclusion types and proved transports, not classification inputs.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.18(5),
printed pp.325–326, and 13.8.16(1b1,b2), p.952 (PDF p.969).
-/

open Subgroup Representation Representation.BinaryOffender Matrix
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
open SourceRestrictions SourceRestrictions.Cases SourceRestrictions.Cases.Exchanged
open PairCoordinates
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement
@[expose] public noncomputable section
attribute [local instance] Exchanged.fixedBinaryAlgebra Exchanged.hermitianBinaryModule
variable {D E V X : Type*} [Group D] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]
  (ρ : Representation (ZMod 2) D V) {K K₀ T : Subgroup D}
  {I : Submodule (ZMod 2) V}

structure PairedCentralIdentification (K : Subgroup D) (t : D)
    (σ : Representation (ZMod 2) E X) where
  first : CentralQuotientIdentification ρ K (subspaceCommutator ρ ⊤ K)
    (subspaceCommutator_invariant ρ ⊤ K) σ
  second : CentralQuotientIdentification ρ (K.conjBy t⁻¹)
    (subspaceCommutator ρ ⊤ (K.conjBy t⁻¹))
    (subspaceCommutator_invariant ρ ⊤ (K.conjBy t⁻¹)) σ
  actors : second.groupEquiv = (ProductMarking.conjugateActor (t := t)).symm.trans first.groupEquiv

theorem changeCentralSpace_groupEquiv {J : Submodule (ZMod 2) V}
    {hI : K ≤ subspaceStabilizer ρ I} {σ : Representation (ZMod 2) E X}
    (d : CentralQuotientIdentification ρ K I hI σ) (h : I = J)
    (hJ : K ≤ subspaceStabilizer ρ J) :
    (changeCentralSpace ρ d h hJ).groupEquiv = d.groupEquiv := by
  subst J
  rfl

def pairedIdentification {t : D} (p : ProductMarking K K₀ t)
    {hI : K₀ ≤ subspaceStabilizer ρ I} {σ : Representation (ZMod 2) E X}
    (hcross : subspaceCommutator ρ I (K.conjBy t⁻¹) = ⊥)
    (hfirst : subspaceCommutator ρ ⊤ K = I)
    (d : HatIdentification ρ K K₀ p.le I hI σ) :
    PairedCentralIdentification ρ K t σ := by
  let a := p.centralIdentification ρ hcross d
  have hsecond : subspaceCommutator ρ ⊤ (K.conjBy t⁻¹) = rightConjugate ρ I t := by
    rw [← right_conjugate_moved ρ t, hfirst]
  refine ⟨changeCentralSpace ρ a hfirst.symm _,
    changeCentralSpace ρ (ProductMarking.conjugateIdentification (t := t) ρ a) hsecond.symm _, ?_⟩
  rw [changeCentralSpace_groupEquiv, changeCentralSpace_groupEquiv]
  rfl

inductive FactorModules (K : Subgroup D) (t : D) (n : ℕ) : Prop
  | natural (F : Type) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
      (card : Nat.card F = 2 ^ n)
      (identification : PairedCentralIdentification ρ K t
        (restrictScalars (specialLinearNatural (k := F) 2)))
  | alternatingFive (exponent : n = 2)
      (identification : PairedCentralIdentification ρ K t alternatingFiveNatural)
  | evenOrthogonal (m : ℕ) [NeZero m] (exponent : n = 2 * m)
      (identification : PairedCentralIdentification ρ K t (SL2.BinarySmall.hermitian m))

structure FactorConclusion (K K₀ : Subgroup D) (t : D) (n : ℕ) : Prop where
  sum : subspaceCommutator ρ ⊤ K ⊔ subspaceCommutator ρ ⊤ (K.conjBy t⁻¹) = ⊤
  exchange : rightConjugate ρ (subspaceCommutator ρ ⊤ K) t =
    subspaceCommutator ρ ⊤ (K.conjBy t⁻¹)
  first_fixed : subspaceCommutator ρ ⊤ K ≤ fixedSpace ρ (K.conjBy t⁻¹)
  second_fixed : subspaceCommutator ρ ⊤ (K.conjBy t⁻¹) ≤ fixedSpace ρ K
  central_disjoint : Disjoint
    ((subspaceCommutator ρ ⊤ K).map (fixedSpace ρ K₀).mkQ)
    ((subspaceCommutator ρ ⊤ (K.conjBy t⁻¹)).map (fixedSpace ρ K₀).mkQ)
  modules : FactorModules ρ K t n

/-- The repository's actual carrier is ClassicalOrthogonal.POmegaPlus. -/
def projectiveNatural (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F] :
    Representation (ZMod 2) (ClassicalOrthogonal.POmegaPlus 2 F)
      (ClassicalOrthogonal.VectorD 2 F) :=
  restrictScalars (ClassicalOrthogonal.projectiveElementaryNatural (ClassicalOrthogonal.formD 2 F))

structure OrthogonalIdentification (K₀ : Subgroup D)
    (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F] where
  groupEquiv : K₀ ≃* ClassicalOrthogonal.POmegaPlus 2 F
  linearEquiv : V ≃ₗ[ZMod 2] ClassicalOrthogonal.VectorD 2 F
  equivariant : ∀ (g : K₀) v, linearEquiv (ρ g v) =
    projectiveNatural F (groupEquiv g) (linearEquiv v)

namespace OrthogonalIdentification
variable {ρ} {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
  (d : OrthogonalIdentification ρ K₀ F) {t : D} (p : ProductMarking K K₀ t)

def markedProduct : K × K ≃* ClassicalOrthogonal.POmegaPlus 2 F := p.product.trans d.groupEquiv

theorem markedProduct_first (k : K) :
    d.markedProduct p (k,1) = d.groupEquiv (inclusion p.le k) := by
  change d.groupEquiv (p.product (k,1)) = _
  exact congrArg d.groupEquiv (Subtype.ext (p.first k))

theorem markedProduct_second (k : K) :
    d.markedProduct p (1,k) = d.groupEquiv
      (inclusion p.conjugate_le (ProductMarking.conjugateActor (t := t) k)) := by
  change d.groupEquiv (p.product (1,k)) = _
  apply congrArg d.groupEquiv
  apply Subtype.ext
  exact (p.second k).trans (ProductMarking.conjugateActor_coe k).symm

/-- Both factors act through the same orthogonal identification. -/
theorem markedProduct_equivariant (a b : K) (v : V) :
    d.linearEquiv (ρ (p.product (a,b)) v) =
      projectiveNatural F (d.markedProduct p (a,b)) (d.linearEquiv v) :=
  d.equivariant _ _
end OrthogonalIdentification

def orthogonalIdentification_of_literal {F : Type*} [Field F] [CharP F 2]
    [Algebra (ZMod 2) F] {hI : K₀ ≤ subspaceStabilizer ρ I}
    (hinv : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ I)
    (hfull : orbitSpan ρ ⊤ I = ⊤)
    (d : LiteralIdentification ρ K₀ I hI (RemainingModels.omegaNatural (F := F))) :
    OrthogonalIdentification ρ K₀ F := by
  have htop : I = ⊤ := (orbitSpan_eq_self ρ hinv).symm.trans hfull
  let e : I ≃ₗ[ZMod 2] V := LinearEquiv.ofTop I htop
  let q := ClassicalOrthogonal.elementaryProjectiveEquiv (ClassicalOrthogonal.formD 2 F)
  refine ⟨d.groupEquiv.trans q, e.symm.trans d.linearEquiv, ?_⟩
  intro g v
  change d.linearEquiv (e.symm (ρ g v)) =
    (projectiveNatural F) (q (d.groupEquiv g)) (d.linearEquiv (e.symm v))
  have he : e.symm (ρ g v) = (invariantSubspace ρ K₀ I hI).toRepresentation g (e.symm v) :=
    Subtype.ext rfl
  rw [he]
  refine (d.equivariant g (e.symm v)).trans ?_
  change RemainingModels.omegaNatural (d.groupEquiv g) _ =
    RemainingModels.omegaNatural (q.symm (q (d.groupEquiv g))) _
  rw [MulEquiv.symm_apply_apply]

inductive Conclusion (K K₀ : Subgroup D) (t : D) (n : ℕ) : Prop
  | factors (data : FactorConclusion ρ K K₀ t n)
  | orthogonal (F : Type) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
      (card : Nat.card F = 2 ^ n) (identification : OrthogonalIdentification ρ K₀ F)

end
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement

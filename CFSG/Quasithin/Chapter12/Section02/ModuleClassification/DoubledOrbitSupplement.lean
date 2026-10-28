module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitCentralizer
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.NormalizerSupplement

/-!
# Offender supplements on a multiplicity-free doubled module

The two different simple constituents kill the two-core of the group
obtained by adjoining an offender to the component image. Its quotient by
that component is a two-group. The complete corrected B.5.1 theorem then
applies to its actual best-offender subgroup, retaining all six clauses.

The generic interface keeps the subgroup and operator constructions small;
DoubledOrbitOffenders supplies the literal Chapter 12 action and coordinates.
Source: Aschbacher--Smith, B.5.1, printed pp.99--103, as used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit
universe u
variable {P W : Type u} [Group P] [IsQuasisimple P]
  [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
  (σ : Representation (ZMod 2) P W) (hf : Function.Injective σ)
  (A : Subgroup (linearNormalizer σ))

include hf

omit [IsQuasisimple P] [Module.Finite (ZMod 2) W] in
private theorem component_kernel : σ.ker ≤ center P := by
  rw [σ.ker_eq_bot_iff.mpr hf]
  exact bot_le

theorem supplement_twoCore_of_pair
    {J U Z : Type*} [Group J]
    [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U]
    [AddCommGroup Z] [Module (ZMod 2) Z] [Module.Finite (ZMod 2) Z]
    (q : J →* P) (α : Representation (ZMod 2) J U)
    (β : Representation (ZMod 2) J Z) [IsIrreducible α] [IsIrreducible β]
    (hne : ¬ Nonempty (α.Equiv β)) (e : W ≃ₗ[ZMod 2] (U × Z))
    (he : ∀ g w, e (σ (q g) w) = (α.prod β) g (e w)) :
    pCore 2 (supplement σ A) = ⊥ := by
  let := component_quasisimple σ (component_kernel σ hf) A
  let := component_normal σ A
  let := supplement_finite σ A
  exact twoCore_eq_bot_of_pair (linearAction (supplement σ A))
    (linearAction_injective _) (component σ A) ((projection σ A).comp q)
    α β hne e he

/-- Trivial two-core is the only module-theoretic input needed to apply the
complete B.5.1 theorem to this literal offender supplement. -/
theorem normalizer_source_of_twoCore [Finite P]
    (hsq : IsSQTK KnownSimple.IsKnownSimple P)
    (hcore : pCore 2 (supplement σ A) = ⊥)
    (hA : IsOffender (normalizerRepresentation σ) A) :
    NormalizerConclusion σ A := by
  let := component_quasisimple σ (component_kernel σ hf) A
  let := component_normal σ A
  let := supplement_finite σ A
  have hq : IsPGroup 2 (supplement σ A ⧸ component σ A) := by
    let B := A.map (linearNormalizer σ).subtype
    let := hA.1.2
    have hb : IsPGroup 2 (B.subgroupOf (supplement σ A)) :=
      (IsElementaryAbelian.isPGroup (p := 2) (G := A)).map _ |>.comap_subtype
    exact quotient_isPGroup_of_sup_eq_top (B.subgroupOf (supplement σ A)) (component σ A) hb
      (by rw [sup_comm]; exact (codisjoint_subgroupOf_sup (actionImage σ) B).eq_top)
  let e : P ≃* component σ A := MulEquiv.ofBijective (projection σ A)
    ⟨fun _ _ he => hf (congrArg (fun k : component σ A =>
      linearAction (supplement σ A) k) he), projection_surjective σ A⟩
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion
    (linearAction (supplement σ A)) (component σ A) hq hcore
    ((IsSQTK.equiv e).mp hsq) (linearAction_injective _) (supplement_ff σ A hA)
end CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit

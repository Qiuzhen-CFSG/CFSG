module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.Arithmetic
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation

/-!
# From a checked mask tree to actual source conjugators

Induction on the parent index realizes every tree node by a word in the
original max2 subgroup. A right-conjugation edge by g extends the left
conjugator w to g⁻¹w. Injectivity of the original kernel products then
transfers distinct mask pairs to distinct actual conjugate pairs.

The arithmetic soundness and finite tree remain explicit independent inputs.
This theorem supplies the final assembly for `pair_orbit_witness` once both
certificates are proved. It does not assert either input.

Source: ATLAS J4G1-max2W1, with attribution in TwoCoreCentralizer/source;
Kleidman–Wilson (1988), pp.484–510; Aschbacher–Smith A.3.12, pp.47–48.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl PairOrbitData

attribute [local irreducible] kernelProduct

private theorem source_action_step (ha : SourceActionLaw)
    (s : Bool) (m n : Fin 8192) (h : maskAction s m.val = n.val) :
    (sourceGenerator s)⁻¹ * kernelProduct m * sourceGenerator s = kernelProduct n := by
  calc
    _ = maskProduct kernelFactor (maskAction s m.val) := ha s m
    _ = maskProduct kernelFactor n.val := congrArg (maskProduct kernelFactor) h
    _ = kernelProduct n := by unfold kernelProduct; rfl

private theorem pairOrbit_inv_mul (g w : sourceSubgroup) :
    pairOrbit (g⁻¹ * w) =
      (g⁻¹ * (pairOrbit w).1 * g, g⁻¹ * (pairOrbit w).2 * g) := by
  simp only [pairOrbit, MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc]

/-- Every node is reached by left conjugation in the original source subgroup. -/
theorem pairOrbit_realize (ha : SourceActionLaw) (c : OrbitCertificate)
    (i : Fin 5544) :
    ∃ w : sourceSubgroup,
      pairOrbit w = (kernelProduct (c.masks i).1, kernelProduct (c.masks i).2) := by
  have all : ∀ n, ∀ i : Fin 5544, i.val = n →
      ∃ w : sourceSubgroup,
        pairOrbit w = (kernelProduct (c.masks i).1, kernelProduct (c.masks i).2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      by_cases hzero : i = 0
      · subst i
        refine ⟨1, ?_⟩
        rw [c.root]
        simp [pairOrbit, sourceP, sourceQ]
      · obtain ⟨w, hw⟩ := ih (c.parent i).val
          ((c.decrease i hzero).trans_eq hi) (c.parent i) rfl
        refine ⟨(sourceGenerator (c.useY i))⁻¹ * w, ?_⟩
        rw [pairOrbit_inv_mul, hw]
        exact Prod.ext
          (source_action_step ha _ _ _ (congrArg Prod.fst (c.edge i hzero)))
          (source_action_step ha _ _ _ (congrArg Prod.snd (c.edge i hzero)))
  exact all i.val i rfl

/-- Final assembly requires both the literal word action and the finite certificate. -/
theorem pair_orbit_witness_of_certificates
    (ha : SourceActionLaw) (c : OrbitCertificate) : PairOrbitWitness := by
  choose w hw using pairOrbit_realize ha c
  refine ⟨w, ?_⟩
  intro i j hij
  apply c.injective
  change pairOrbit (w i) = pairOrbit (w j) at hij
  rw [hw i, hw j] at hij
  have hp := congrArg Prod.fst hij
  have hq := congrArg Prod.snd hij
  exact Prod.ext
    (@kernelProduct_injective (c.masks i).1 (c.masks j).1 hp)
    (@kernelProduct_injective (c.masks i).2 (c.masks j).2 hq)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer

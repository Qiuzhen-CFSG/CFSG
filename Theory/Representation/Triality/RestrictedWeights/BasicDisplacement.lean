module

public import Theory.Representation.Triality.RestrictedWeights.BasicDisplacement.RootOperators
public import Theory.Representation.Triality.RestrictedWeights.BasicDisplacement.WeightSpacePairs
public import Theory.Representation.Triality.RestrictedWeights.ConcreteTensorDisplacement

/-!
# Actual basic-module displacement for the two triality root involutions

The constructed restricted D4 modules contain their literal highest weights.
The four concrete Weyl normalizers propagate these weights. For each of the
fifteen nonzero binary weights, the checked lattice witnesses give two disjoint
exchanged pairs for both the central reflection and the three-arm reflection.
For each nonzero diagram-fixed weight they give six pairs. Independent torus
weight spaces make the corresponding action-minus-identity vectors independent.
The actual Spin conjugacies then yield the required root displacement ranks.

The final consumer applies these bounds to the original twisted tensor and
proves its strict 5n estimate. It also discharges coefficient-Frobenius fixity,
since every root parameter is one. The finite realization, original marking,
and weight-period data remain with their existing source producers; no rank,
module classification, or dimension-to-displacement premise is assumed here.

Source: Guralnick--Malle II, Lemma 8.6; GLS3 §§1.12, 1.14 and 2.8.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction
open Representation.BinaryOffender.NaturalTensor
namespace Triality.RestrictedWeights.BasicDisplacement
noncomputable section
universe u v
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

local instance : AlgebraicGroup (Concrete.finiteGeometry k hu).torus.carrierVariety :=
  (Concrete.finiteGeometry k hu).torus.carrierAlgebraicGroup

private theorem weight_character (i : Fin 4) (a : Weight)
    (t : (Concrete.finiteGeometry k hu).torus.carrierVariety.Point) :
    ((Concrete.finiteGeometry k hu).leftWeightEmbedding (reflection i a)).pointCharacter t =
      ((Concrete.finiteGeometry k hu).leftWeightEmbedding a).pointCharacter
        ((CorootTorus.torusReflection k i).onPoints t) := by
  apply (Concrete.finiteGeometry k hu).leftWeightEmbedding_reflection
    (fun i => (CorootTorus.torusReflection k i).onPoints) ?_ i a t
  intro j b s
  change (Concrete.weightEquiv k (Multiplicative.ofAdd (reflection j b))).pointCharacter s =
    (Concrete.weightEquiv k (Multiplicative.ofAdd b)).pointCharacter _
  rw [Concrete.weightEquiv_apply,Concrete.weightEquiv_apply]
  exact CorootTorus.weightEmbedding_reflection k j b s

variable {V : Type v} [AddCommGroup V] [Module k V]

private theorem normalizer_mem_weight (ρ : RationalRepresentation (groupVariety k) V)
    (i : Fin 4) (a : Weight) (v : V)
    (hv : v ∈ weightSpace ρ (Concrete.finiteGeometry k hu).torus
      ((Concrete.finiteGeometry k hu).leftWeightEmbedding a)) :
    (ρ.action (simpleNormalizer k i)).val v ∈
      weightSpace ρ (Concrete.finiteGeometry k hu).torus
        ((Concrete.finiteGeometry k hu).leftWeightEmbedding (reflection i a)) := by
  intro t
  calc
    (ρ.action ((Concrete.finiteGeometry k hu).torus.includePoint t)).val
        ((ρ.action (simpleNormalizer k i)).val v) =
      (ρ.action ((Concrete.finiteGeometry k hu).torus.includePoint t * simpleNormalizer k i)).val v := by
        rw [map_mul]; rfl
    _ = (ρ.action (simpleNormalizer k i *
        (Concrete.finiteGeometry k hu).torus.includePoint
          ((CorootTorus.torusReflection k i).onPoints t))).val v := by
      exact congrArg (fun g => (ρ.action g).val v)
        (CorootTorus.torusReflection_conjugation k i t)
    _ = ((Concrete.finiteGeometry k hu).leftWeightEmbedding a).pointCharacter
        ((CorootTorus.torusReflection k i).onPoints t) •
          (ρ.action (simpleNormalizer k i)).val v := by
      rw [map_mul]
      change (ρ.action (simpleNormalizer k i)).val
        ((ρ.action _).val v) = _
      exact (congrArg (fun z => (ρ.action (simpleNormalizer k i)).val z)
        (hv ((CorootTorus.torusReflection k i).onPoints t))).trans (map_smul _ _ _)
    _ = _ := by rw [weight_character]

private theorem weyl_mem_weight (ρ : RationalRepresentation (groupVariety k) V)
    (short : Bool) (a : Weight) (v : V)
    (hv : v ∈ weightSpace ρ (Concrete.finiteGeometry k hu).torus
      ((Concrete.finiteGeometry k hu).leftWeightEmbedding a)) :
    (ρ.action (weylOperator k short)).val v ∈
      weightSpace ρ (Concrete.finiteGeometry k hu).torus
        ((Concrete.finiteGeometry k hu).leftWeightEmbedding (reflect short a)) := by
  cases short
  · exact normalizer_mem_weight k hu ρ 1 a v hv
  · simpa only [weylOperator,reflect,↓reduceIte,map_mul,Units.val_mul,Module.End.mul_apply] using
      normalizer_mem_weight k hu ρ 0 _ _
        (normalizer_mem_weight k hu ρ 2 _ _ (normalizer_mem_weight k hu ρ 3 a v hv))

variable [FiniteDimensional k V]

private theorem root_fixedCodim_eq_weyl
    (ρ : RationalRepresentation (groupVariety k) V) (short : Bool) :
    operatorFixedCodim ((ρ.action (rootOperator k short)).val) =
      operatorFixedCodim ((ρ.action (weylOperator k short)).val) := by
  apply operatorFixedCodim_eq_of_equiv _ _
    (ρ.action (rootConjugator k short)).toLinearEquiv
  intro v
  change (ρ.action (rootConjugator k short)).val
    ((ρ.action (rootOperator k short)).val v) =
    (ρ.action (weylOperator k short)).val ((ρ.action (rootConjugator k short)).val v)
  have he : rootConjugator k short * rootOperator k short =
      weylOperator k short * rootConjugator k short := by
    rw [← rootOperator_conjugate]
    group
  change ((ρ.action (rootConjugator k short) * ρ.action (rootOperator k short)).val :
    Module.End k V) v = ((ρ.action (weylOperator k short) *
      ρ.action (rootConjugator k short)).val : Module.End k V) v
  rw [← map_mul,← map_mul,he]

omit [FiniteDimensional k V] in
private theorem reflection_support (ρ : RationalRepresentation (groupVariety k) V)
    (i : Fin 4) (a : Weight)
    (ha : weightSpace ρ (Concrete.finiteGeometry k hu).torus
      ((Concrete.finiteGeometry k hu).leftWeightEmbedding a) ≠ ⊥) :
    weightSpace ρ (Concrete.finiteGeometry k hu).torus
      ((Concrete.finiteGeometry k hu).leftWeightEmbedding (reflection i a)) ≠ ⊥ :=
  d4_weightSpace_reflection_of_conjugation ρ _ _ (simpleNormalizer k)
    (fun i => (CorootTorus.torusReflection k i).onPoints)
    (CorootTorus.torusReflection_conjugation k) (weight_character k hu) i a ha

theorem basic_root_displacement (short : Bool) (a : BasicWeight) (ha : a ≠ zeroWeight) :
    2 ≤ operatorFixedCodim (((Concrete.basicFamily k hu).factor a).action.action
      (rootOperator k short)).val ∧
    (diagramAction a = a →
      6 ≤ operatorFixedCodim (((Concrete.basicFamily k hu).factor a).action.action
        (rootOperator k short)).val) := by
  let A := (Concrete.basicFamily k hu).factor a
  let ρ := A.action
  let S := Concrete.finiteGeometry k hu
  obtain ⟨v,hv⟩ := (Concrete.basicFamily k hu).highest a
  have hh : weightSpace ρ S.torus (S.leftWeightEmbedding (coefficient a)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨v,hv.2.2,hv.1.1⟩
  have hpair (i : Fin 6) :
      weightSpace ρ S.torus (S.leftWeightEmbedding (pairWeight short a i)) ≠ ⊥ :=
    pairWeight_mem (reflection_support k hu ρ) hh short i
  rw [root_fixedCodim_eq_weyl k ρ short]
  constructor
  · exact rank_ge_of_weight_pairs ρ S.torus S.leftWeightEmbedding (weylOperator k short)
      (fun i => pairWeight short a (Fin.castLE (by decide : 2≤6) i))
      (fun i => reflect short (pairWeight short a (Fin.castLE (by decide : 2≤6) i)))
      (twoWeights_injective short a ha) (fun i => hpair _)
      (fun i w hw => weyl_mem_weight k hu ρ short _ w hw)
  · intro hf
    exact rank_ge_of_weight_pairs ρ S.torus S.leftWeightEmbedding (weylOperator k short)
      (pairWeight short a) (fun i => reflect short (pairWeight short a i))
      (sixWeights_injective short a ha hf) hpair
      (fun i w hw => weyl_mem_weight k hu ρ short _ w hw)


/-- The literal triality tensor consumer, with all basic displacement premises discharged. -/
theorem five_mul_lt_basic_root_tensor_displacement
    {G : Type v} [Group G] (ι : G →* Variety.Point (groupVariety k))
    (t : G) (ht : t^2=1) (short : Bool) (hmark : ι t = rootOperator k short)
    (w : ℕ → BasicWeight) (n s : ℕ) (hn : 0<n) (hs : 0<s) (hsn : s ∣ 3*n)
    (hwrap : ∀ i,w (i+n)=diagramAction (w i)) (hp : Function.Periodic w s)
    (hne : ∃ i,w i≠zeroWeight) :
    5*n < s*operatorFixedCodim ((tensor (Concrete.basicFamily k hu).factor
      (Concrete.finiteGeometry k hu).frobenius.onPoints ι w n).ρ t) := by
  have hφ : (Concrete.finiteGeometry k hu).frobenius.onPoints (ι t)=ι t := by
    rw [hmark]
    change (regularFrobeniusLift k 1).onPoints (rootOperator k short) = _
    cases short <;>
      simp only [rootOperator,Bool.false_eq_true,↓reduceIte,map_mul,
        regularFrobeniusLift_onPoints,GraphField.frobenius_rootPoint,one_pow]
  apply Concrete.five_mul_lt_basic_tensor_displacement k hu ι t ht hφ
    w n s hn hs hsn hwrap hp hne
  intro a ha
  rw [hmark]
  exact basic_root_displacement k hu short a ha

end
end Triality.RestrictedWeights.BasicDisplacement

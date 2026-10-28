module
public import Theory.Representation.Triality.RestrictedWeights.BasicDisplacement

/-!
# Strong short-root displacement for the K.3 triality branch

Four exchanged Weyl weights give four moved dimensions in every nonzero
basic D4 module. Eleven pairs give eleven moved dimensions for each nonzero
diagram-fixed weight. The witnesses use the actual left simple-coroot
coordinates and three-arm Weyl operator. This strengthens the FF estimate
for the cubic-source consumer without assuming natural or adjoint recognition.
Source: Guralnick--Malle II, Lemma 8.6; Aschbacher--Smith K.3, p.457.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction
open Triality.RestrictedWeights.BasicDisplacement
open Triality.RestrictedWeights
open Representation.BinaryOffender.NaturalTensor
namespace CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions.TrialityWeights
noncomputable section

private def elevenIndices (a : BasicWeight) : Fin 11 → Fin 25 :=
  if a 0 then
    if a 1 then ![0,1,2,3,4,8,10,11,12,13,14]
    else ![0,2,3,4,8,10,11,12,13,14,15]
  else ![1,2,3,4,8,10,11,13,16,17,18]

private def elevenWeight (a : BasicWeight) (i : Fin 11) : Weight :=
  wordAction (coefficient a) (words[elevenIndices a i])

private theorem four_injective : ∀ (a : BasicWeight), a ≠ zeroWeight →
    Function.Injective (Sum.elim
      (fun i : Fin 4 => pairWeight true a (Fin.castLE (by decide) i))
      (fun i : Fin 4 => reflect true (pairWeight true a (Fin.castLE (by decide) i)))) := by
  decide +kernel

private theorem eleven_injective : ∀ (a : BasicWeight), a ≠ zeroWeight →
    diagramAction a = a → Function.Injective (Sum.elim
      (elevenWeight a) (fun i => reflect true (elevenWeight a i))) := by
  decide +kernel

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

theorem basic_short_displacement (a : BasicWeight) (ha : a ≠ zeroWeight) :
    4 ≤ operatorFixedCodim (((Triality.RestrictedWeights.Concrete.basicFamily k hu).factor a).action.action
      (rootOperator k true)).val ∧
    (diagramAction a = a →
      11 ≤ operatorFixedCodim (((Triality.RestrictedWeights.Concrete.basicFamily k hu).factor a).action.action
        (rootOperator k true)).val) := by
  let A := (Triality.RestrictedWeights.Concrete.basicFamily k hu).factor a
  let ρ := A.action
  let S := Triality.RestrictedWeights.Concrete.finiteGeometry k hu
  obtain ⟨v,hv⟩ := (Triality.RestrictedWeights.Concrete.basicFamily k hu).highest a
  have hh : weightSpace ρ S.torus (S.leftWeightEmbedding (coefficient a)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨v,hv.2.2,hv.1.1⟩
  rw [root_fixedCodim_eq_weyl k ρ true]
  constructor
  · exact rank_ge_of_weight_pairs ρ S.torus S.leftWeightEmbedding (weylOperator k true)
      (fun i : Fin 4 => pairWeight true a (Fin.castLE (by decide) i))
      (fun i : Fin 4 => reflect true (pairWeight true a (Fin.castLE (by decide) i)))
      (four_injective a ha)
      (fun i => pairWeight_mem (reflection_support k hu ρ) hh true _)
      (fun i w hw => weyl_mem_weight k hu ρ true _ w hw)
  · intro hf
    exact rank_ge_of_weight_pairs ρ S.torus S.leftWeightEmbedding (weylOperator k true)
      (elevenWeight a) (fun i => reflect true (elevenWeight a i))
      (eleven_injective a ha hf)
      (fun i => wordAction_mem (reflection_support k hu ρ) hh _)
      (fun i w hw => weyl_mem_weight k hu ρ true _ w hw)

end
end CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions.TrialityWeights

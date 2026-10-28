module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Factors
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Basic

/-!
# Ordering the factors with the natural rank-two seed

In the binary natural seven-point module, a two-dimensional subspace invariant
under the four-plus-three stabilizer cannot be fixed by the three-point cycle.
Indeed, the six transpositions on the four-point block carry every nonconstant
vector to at least four distinct nonzero vectors. A binary plane has only three
nonzero vectors. The cycle-fixed even-weight vectors constant on the four-point
block form a line, which cannot contain a plane. The small coordinate calculation
below is checked by the kernel on all 128 vectors of the full permutation module.

Transport through the equivariant identification for the specified action map
then excludes the reversed marking. Thus L₁,+ is the three-point factor and L₀
is the literal O² residual in `Factors.lean`. Naturality, the unordered marking,
and the full local image remain explicit inputs for the source assembly. The
rank and local invariance already suffice here, so the seed's commutator identity
and faithfulness or surjectivity of the ambient action map are unnecessary.

Source: Aschbacher–Smith, 13.8.24, printed p.959/PDF p.976
(combined manuscript, 1 March 2004).
-/

public section
open Equiv Subgroup Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection

-- All transpositions on the four-point block, viewed in the actual seven-point action.
private def fourSwap : Fin 6 → S7 :=
  ![swap 0 1, swap 0 2, swap 0 3, swap 1 2, swap 1 3, swap 2 3]

-- Include zero so that the orbit size is bounded by the whole seed cardinality.
private def vectorOrbit (v : Full (Fin 7)) : Finset (Full (Fin 7)) :=
  insert 0 (Finset.univ.image fun i : Fin 6 => representation (Fin 7) (fourSwap i) v)

-- A cycle-fixed even-weight vector with at most four such images is on the fixed line.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem finite_test : ∀ v : Full (Fin 7),
    (∑ i, v i) = 0 → representation (Fin 7) cycle456 v = v →
    (vectorOrbit v).card ≤ 4 → v = fun i => if i.val < 4 then v 0 else 0 := by
  decide +kernel

private theorem fourSwap_mem (i : Fin 6) : fourSwap i ∈ fourThreeStabilizer := by
  fin_cases i <;> decide +kernel

/-- The finite obstruction in the literal binary natural seven-point module. -/
theorem natural_seed_not_fixed_threeFactor
    (D : Submodule (ZMod 2) (core (Fin 7)))
    (hdim : Module.finrank (ZMod 2) D = 2)
    (hstable : fourThreeStabilizer ≤ subspaceStabilizer (coreRepresentation (Fin 7)) D)
    (hfix : D ≤ fixedSpace (coreRepresentation (Fin 7)) threeFactor) : False := by
  classical
  let : Fintype D := Fintype.ofFinite D
  have hcard : Fintype.card D = 4 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), hdim]
    decide
  let f : D → Full (Fin 7) := fun v => v.val.val
  have hf : Function.Injective f := fun v w h => Subtype.ext (Subtype.ext h)
  have hform (v : D) : f v = fun i => if i.val < 4 then f v 0 else 0 := by
    apply finite_test (f v) v.val.property
    · exact congrArg Subtype.val (hfix v.property ⟨cycle456, mem_zpowers cycle456⟩)
    · have horbit : vectorOrbit (f v) ⊆ Finset.univ.image f := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
        · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
          exact Finset.mem_image.mpr
            ⟨⟨coreRepresentation (Fin 7) (fourSwap i) v.val,
              (hstable (fourSwap_mem i) v.val).mpr v.property⟩, Finset.mem_univ _, rfl⟩
      calc
        (vectorOrbit (f v)).card ≤ (Finset.univ.image f).card := Finset.card_le_card horbit
        _ = Fintype.card D := by rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
        _ = 4 := hcard
  have hinj : Function.Injective (fun v : D => f v 0) := by
    intro v w hvw
    apply hf
    change f v 0 = f w 0 at hvw
    rw [hform v, hform w, hvw]
  have hle := Fintype.card_le_of_injective _ hinj
  have htwo : Fintype.card (ZMod 2) = 2 := by decide
  omega

variable {J E : Type*} [Group J] [AddCommGroup E] [Module (ZMod 2) E]

/-- The natural rank-two seed orders the source's unordered factors through the
same seven-point homomorphism. The local image and invariance are essential;
no commutator or residual-to-A₄ identification is needed for this implication. -/
theorem ordered_marking_of_natural_seed
    (ρ : Representation (ZMod 2) J E) (φ : J →* S7)
    (L₀ X T : Subgroup J)
    (hnatural : PairsBranch.ModuleSelection.IsNatural ρ φ)
    (hmark : MarkedFactors φ L₀ X)
    (D : Submodule (ZMod 2) E) (hdim : Module.finrank (ZMod 2) D = 2)
    (hfix : D ≤ fixedSpace ρ L₀)
    (hstable : (L₀ ⊔ X) ⊔ T ≤ subspaceStabilizer ρ D)
    (hlocal : ((L₀ ⊔ X) ⊔ T).map φ = fourThreeStabilizer) :
    X.map φ = threeFactor ∧ L₀.map φ = fourResidualFactor := by
  rcases hmark with ⟨h₀, _⟩ | ⟨h₀, hX⟩
  · exfalso
    obtain ⟨e, he⟩ := hnatural.linearEquiv
    let D' := D.map e.symm.toLinearMap
    have hdim' : Module.finrank (ZMod 2) D' = 2 := by
      rw [← (e.symm.submoduleMap D).finrank_eq]
      exact hdim
    apply natural_seed_not_fixed_threeFactor D' hdim'
    · apply le_subspaceStabilizer
      intro g hg w hw
      obtain ⟨j, hj, rfl⟩ : g ∈ ((L₀ ⊔ X) ⊔ T).map φ := hlocal.symm ▸ hg
      obtain ⟨v, hv, rfl⟩ := hw
      refine ⟨ρ j v, (hstable hj v).mpr hv, ?_⟩
      apply e.injective
      simp only [LinearEquiv.coe_coe, e.apply_symm_apply, he]
    · rintro w ⟨v, hv, rfl⟩ ⟨g, hg⟩
      obtain ⟨j, hj, rfl⟩ : g ∈ L₀.map φ := h₀.symm ▸ hg
      change coreRepresentation (Fin 7) (φ j) (e.symm v) = e.symm v
      apply e.injective
      rw [he, e.apply_symm_apply]
      exact hfix hv ⟨j, hj⟩
  · exact ⟨hX, h₀⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection

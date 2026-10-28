module

public import Theory.Representation.InvertedCubicTensor
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage

/-!
# The natural planes from a basis of the cubic multiplicity space

The inverted-cubic tensor equivalence turns a chosen basis of the
transposition-fixed plane into two complementary natural S₃ planes. Their
nonzero vectors form single orbits. Thus involutory lifts of the two basis
vectors construct elementary preimages, on the original coordinate map.

Source: Aschbacher–Smith 14.3.18(4), printed p.996, following 12.8.9(3).
-/

@[expose] public section
noncomputable section
open scoped TensorProduct

namespace InvertedCubicTensor
abbrev NaturalPlane := BinaryPermutation.core (Fin 3)

private instance : Fintype NaturalPlane :=
  @Subtype.fintype _ _
    (fun x => inferInstanceAs (Decidable (∑ i : Fin 3, x i = 0)))
    (inferInstance : Fintype (Fin 3 → ZMod 2))

theorem naturalPlane_card : Nat.card NaturalPlane = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem naturalPlane_transitive (u v : NaturalPlane) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : S₃, BinaryPermutation.coreRepresentation (Fin 3) g u = v := by
  have cert : ∀ u v : NaturalPlane, u ≠ 0 → v ≠ 0 →
      v = u ∨ v = BinaryPermutation.coreRepresentation (Fin 3) cubic u ∨
      v = BinaryPermutation.coreRepresentation (Fin 3) (cubic*cubic) u := by
    decide +kernel
  rcases cert u v hu hv with he | he | he
  · exact ⟨1, by simpa using he.symm⟩
  · exact ⟨cubic, he.symm⟩
  · exact ⟨cubic*cubic, he.symm⟩

variable {W : Type*} [AddCommGroup W] [Module F W]
  (σ : Representation F S₃ W) (hfree : ∀ w, σ cubic w = w → w = 0)
  (b : Module.Basis (Fin 2) F (multiplicitySpace σ))

def naturalFactorCoordinates : W ≃ₗ[F] (Fin 2 →₀ NaturalPlane) :=
  (tensorEquiv σ hfree).symm.trans (TensorProduct.equivFinsuppOfBasisLeft b)

def naturalFactor (i : Fin 2) : NaturalPlane →ₗ[F] W :=
  (naturalFactorCoordinates σ hfree b).symm.toLinearMap.comp (Finsupp.lsingle i)

theorem naturalFactor_tmul (i : Fin 2) (v : NaturalPlane) :
    naturalFactor σ hfree b i v = tensorEquiv σ hfree (b i ⊗ₜ[F] v) := by
  simp [naturalFactor,naturalFactorCoordinates]

theorem naturalFactor_injective (i : Fin 2) :
    Function.Injective (naturalFactor σ hfree b i) := by
  intro v w hvw
  have hh := congrArg (fun x => naturalFactorCoordinates σ hfree b x i) hvw
  simpa [naturalFactor] using hh

theorem naturalFactor_equivariant (i : Fin 2) (g : S₃) (v : NaturalPlane) :
    naturalFactor σ hfree b i (BinaryPermutation.coreRepresentation (Fin 3) g v) =
      σ g (naturalFactor σ hfree b i v) := by
  rw [naturalFactor_tmul,naturalFactor_tmul]
  exact tensorEquiv_symmetric σ hfree g (b i) v

def naturalFactorRepresentation {K : Type*} [Group K] (π : K →* S₃) (i : Fin 2) :
    Subrepresentation (σ.comp π) where
  toSubmodule := (naturalFactor σ hfree b i).range
  apply_mem_toSubmodule k := by
    rintro _ ⟨v,rfl⟩
    exact ⟨_, naturalFactor_equivariant σ hfree b i (π k) v⟩

theorem naturalFactorRepresentation_card {K : Type*} [Group K]
    (π : K →* S₃) (i : Fin 2) :
    Nat.card (naturalFactorRepresentation σ hfree b π i).toSubmodule = 4 := by
  change Nat.card (naturalFactor σ hfree b i).range = 4
  rw [← Nat.card_congr (LinearEquiv.ofInjective (naturalFactor σ hfree b i)
    (naturalFactor_injective σ hfree b i)).toEquiv]
  exact naturalPlane_card

theorem naturalFactorRepresentation_transitive {K : Type*} [Group K]
    (π : K →* S₃) (hπ : Function.Surjective π) (i : Fin 2)
    (u v : (naturalFactorRepresentation σ hfree b π i).toSubmodule)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ k : K, (naturalFactorRepresentation σ hfree b π i).toRepresentation k u = v := by
  obtain ⟨a,ha⟩ := u.property
  obtain ⟨c,hc⟩ := v.property
  have ha0 : a ≠ 0 := by
    intro h
    apply hu
    apply Subtype.ext
    simpa [h] using ha.symm
  have hc0 : c ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    simpa [h] using hc.symm
  obtain ⟨g,hg⟩ := naturalPlane_transitive a c ha0 hc0
  obtain ⟨k,hk⟩ := hπ g
  refine ⟨k, ?_⟩
  apply Subtype.ext
  change σ (π k) u.val = v.val
  rw [hk,← ha,← hc,← naturalFactor_equivariant,hg]

theorem naturalFactorRepresentation_isCompl {K : Type*} [Group K] (π : K →* S₃) :
    IsCompl (naturalFactorRepresentation σ hfree b π 0).toSubmodule
      (naturalFactorRepresentation σ hfree b π 1).toSubmodule := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro w hw0 hw1
    obtain ⟨v,hv⟩ := hw0
    obtain ⟨z,hz⟩ := hw1
    have he := congrArg (fun x => naturalFactorCoordinates σ hfree b x 0)
      (hv.trans hz.symm)
    have hv0 : v = 0 := by simpa [naturalFactor] using he
    simpa [hv0] using hv.symm
  · apply codisjoint_iff.mpr
    apply top_unique
    intro w _
    let c := naturalFactorCoordinates σ hfree b w
    have hc : c = Finsupp.single 0 (c 0) + Finsupp.single 1 (c 1) := by
      ext i
      fin_cases i <;> simp
    refine Submodule.mem_sup.mpr ⟨naturalFactor σ hfree b 0 (c 0), ⟨_,rfl⟩,
      naturalFactor σ hfree b 1 (c 1), ⟨_,rfl⟩, ?_⟩
    apply (naturalFactorCoordinates σ hfree b).injective
    simpa [naturalFactor] using hc.symm

def naturalFactorSeed : NaturalPlane := ⟨![1,1,0], by
  change ∑ i : Fin 3, (![1,1,0] : Fin 3 → ZMod 2) i = 0
  decide⟩

theorem naturalFactor_seed (i : Fin 2) :
    naturalFactor σ hfree b i naturalFactorSeed = (b i : W) := by
  rw [naturalFactor_tmul,tensorEquiv_tmul]
  simp [naturalFactorSeed]

end InvertedCubicTensor

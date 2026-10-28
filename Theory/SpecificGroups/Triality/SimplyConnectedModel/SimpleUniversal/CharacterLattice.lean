module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus
public import Theory.AlgebraicGroup.Tori.Character.Duality
import Mathlib.Tactic

/-!
# The full integral character lattice of the pinned Spin torus

The regular simple-coroot torus isomorphism transports the classification of
Laurent characters to an additive equivalence with Z^4. It extends the
published weight embedding and makes the actual fundamental characters a
basis. The displayed integral matrix is twice the inverse D4 Cartan matrix;
its checked multiplication proves that twice every algebraic character is
in the integral span of the actual simple-root characters.

These are geometric character-lattice statements on the concrete torus.
They do not assert the whole-group isogeny comparison needed for universality.
Source: GLS3, 1.12.5(b,c) and 1.14.1-2,
`refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
noncomputable section
namespace Triality.SimplyConnected
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Pinning
open scoped BigOperators
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Every algebraic character of the concrete torus is one of the integral weights. -/
theorem weightEmbedding_surjective : Function.Surjective (CorootTorus.weightEmbedding k) := by
  intro χ
  obtain ⟨a, ha⟩ := dLaurentCharacter_surjective 4 (χ.comp (CorootTorus.coordinateIso k).hom)
  refine ⟨a, ?_⟩
  apply Morphism.ext
  funext t
  obtain ⟨x, rfl⟩ := (CorootTorus.coordinateIso k).toMulEquiv.surjective t
  apply (dPointEquiv 1).injective
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change dPointEquiv 1 ((CorootTorus.weightEmbedding k a).onPoints
      ((CorootTorus.coordinateIso k).hom.onPoints x)) 0 =
    dPointEquiv 1 (χ.onPoints ((CorootTorus.coordinateIso k).hom.onPoints x)) 0
  rw [CorootTorus.weightEmbedding_apply]
  have h := congrArg (fun f : TorusCharacter (dVariety k 4) =>
    dPointEquiv 1 (f.onPoints x) 0) ha
  rw [dLaurentCharacter_apply] at h
  exact h

/-- All algebraic characters, in the integral coordinates dual to the simple coroots. -/
def characterLatticeEquiv : (Fin 4 → ℤ) ≃+ Additive (TorusWeight (CorootTorus.closedSubgroup k)) where
  toEquiv := Equiv.ofBijective (fun a => Additive.ofMul (CorootTorus.weightEmbedding k a))
    ⟨(CorootTorus.weightEmbedding k).injective, weightEmbedding_surjective k⟩
  map_add' := by
    intro a b
    change CorootTorus.weightEmbedding k (a + b) =
      CorootTorus.weightEmbedding k a * CorootTorus.weightEmbedding k b
    apply Morphism.ext
    funext t
    obtain ⟨x, rfl⟩ := (CorootTorus.coordinateIso k).toMulEquiv.surjective t
    apply (dPointEquiv 1).injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change dPointEquiv 1 ((CorootTorus.weightEmbedding k (a + b)).onPoints
        ((CorootTorus.coordinateIso k).hom.onPoints x)) 0 =
      dPointEquiv 1 (((CorootTorus.weightEmbedding k a).onPoints
        ((CorootTorus.coordinateIso k).hom.onPoints x)) *
        ((CorootTorus.weightEmbedding k b).onPoints
          ((CorootTorus.coordinateIso k).hom.onPoints x))) 0
    rw [CorootTorus.weightEmbedding_apply, dPointEquiv_mul]
    simp only [Pi.mul_apply, CorootTorus.weightEmbedding_apply, Pi.add_apply,
      zpow_add, Finset.prod_mul_distrib]

/-- The full lattice equivalence extends the published weight embedding. -/
theorem characterLatticeEquiv_apply (a : Fin 4 → ℤ) :
    characterLatticeEquiv k a = Additive.ofMul (CorootTorus.weightEmbedding k a) := by
  rfl

/-- The four fundamental algebraic characters form an integral basis. -/
def fundamentalCharacterBasis :
    Module.Basis (Fin 4) ℤ (Additive (TorusWeight (CorootTorus.closedSubgroup k))) :=
  (Pi.basisFun ℤ (Fin 4)).map (characterLatticeEquiv k).toIntLinearEquiv

/-- The basis uses exactly the published fundamental characters. -/
theorem fundamentalCharacterBasis_apply (i : Fin 4) :
    fundamentalCharacterBasis k i = Additive.ofMul (CorootTorus.fundamentalCharacter k i) := by
  change characterLatticeEquiv k ((Pi.basisFun ℤ (Fin 4)) i) = _
  rw [Pi.basisFun_apply, characterLatticeEquiv_apply]
  change CorootTorus.weightEmbedding k (Pi.single i 1) = CorootTorus.fundamentalCharacter k i
  apply TorusCharacter.pointCharacter_injective
  ext t
  obtain ⟨x, rfl⟩ := (CorootTorus.coordinateIso k).toMulEquiv.surjective t
  change (CorootTorus.weightEmbedding k (Pi.single i 1)).pointCharacter
      ((CorootTorus.coordinateIso k).hom.onPoints x) =
    (CorootTorus.fundamentalCharacter k i).pointCharacter
      ((CorootTorus.coordinateIso k).hom.onPoints x)
  rw [CorootTorus.coordinateIso_hom_apply, CorootTorus.weightEmbedding_parameter,
    CorootTorus.fundamentalCharacter_parameter]
  classical
  simp [Pi.single_apply]

/-- Twice the inverse Cartan matrix, with central vertex 1 and arms 0, 2, 3. -/
def twiceCartanInverse : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 2, 1, 1; 2, 4, 2, 2; 1, 2, 2, 1; 1, 2, 1, 2]

/-- Twice any integral weight is the displayed integral combination of Cartan rows. -/
theorem two_smul_eq_cartan_combination (a : Fin 4 → ℤ) :
    (2 : ℤ) • a = ∑ i : Fin 4,
      (∑ j : Fin 4, a j * twiceCartanInverse j i) • typeDCartanMatrix 2 i := by
  have hcoeff : ∀ j l : Fin 4,
      (∑ i : Fin 4, twiceCartanInverse j i * typeDCartanMatrix 2 i l) =
        if j = l then 2 else 0 := by decide
  funext l
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, hcoeff]
  simp [mul_comm]

/-- The Cartan identity on the actual algebraic simple-root characters. -/
theorem character_twice_eq_simple_root_combination (a : Fin 4 → ℤ) :
    (2 : ℤ) • Additive.ofMul (CorootTorus.weightEmbedding k a) =
      ∑ i : Fin 4, (∑ j : Fin 4, a j * twiceCartanInverse j i) •
        Additive.ofMul ((pinnedRootData k).rootWeight (pinnedRootIndex k (simpleRoot i))) := by
  simpa only [map_sum, map_zsmul, characterLatticeEquiv_apply,
    pinnedRootData_rootWeight_simple] using
      congrArg (characterLatticeEquiv k) (two_smul_eq_cartan_combination a)

/-- The integral span of the four actual pinned simple-root characters. -/
def simpleRootCharacterSpan :
    Submodule ℤ (Additive (TorusWeight (CorootTorus.closedSubgroup k))) :=
  Submodule.span ℤ (Set.range fun i : Fin 4 =>
    Additive.ofMul ((pinnedRootData k).rootWeight (pinnedRootIndex k (simpleRoot i))))

/-- The quotient of the character lattice by its simple-root span is killed by two. -/
theorem two_smul_mem_simpleRootCharacterSpan
    (χ : Additive (TorusWeight (CorootTorus.closedSubgroup k))) :
    (2 : ℤ) • χ ∈ simpleRootCharacterSpan k := by
  obtain ⟨a, rfl⟩ := (characterLatticeEquiv k).surjective χ
  rw [characterLatticeEquiv_apply, character_twice_eq_simple_root_combination]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self i)

end Triality.SimplyConnected

module

public import Theory.Representation.G2.RestrictedModules.NaturalHighestWeight
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# A concrete highest-weight orbit for the level-two G₂ Steinberg module

Inside the tensor cube of the actual six-dimensional natural module, take the
orbit span of `e₀ ⊗ (e₀ ⊗ e₁ + e₁ ⊗ e₀)`. This gives a genuine representation
of the split-octonion automorphism group, with a nonzero vector fixed by all six
positive root groups. Its character on `torus l m` is `l²*m`, and its pairings
with the marked short and long coroots are both one.

This construction is independent of the adjoint branch. Identification of this
orbit span as the 64-dimensional irreducible Steinberg factor requires the
separate dimension and simplicity proofs; neither is assumed here.

Source: GLS3, 2.8.6, 2.8.7 and Example 2.8.10(g). The root conventions and
natural representation come from the attributed ATLAS split-octonion model.
-/

@[expose] public noncomputable section

namespace Atlas.G2.Restricted.Steinberg

open scoped TensorProduct BigOperators
open NaturalCoordinates

variable (F : Type*) [Field F] [CharP F 2]

/-- The tensor cube of the actual natural module in its published coordinates. -/
abbrev Ambient := NaturalCoordinates.Space F ⊗[F]
  (NaturalCoordinates.Space F ⊗[F] NaturalCoordinates.Space F)

/-- The tensor cube action of the actual octonion automorphism group. -/
def ambientAction : Representation F (Model F) (Ambient F) :=
  (NaturalCoordinates.action F).tprod
    ((NaturalCoordinates.action F).tprod (NaturalCoordinates.action F))

/-- A pure cube tensor, with the last two factors parenthesized together. -/
def pure (x y z : NaturalCoordinates.Space F) : Ambient F := x ⊗ₜ[F] (y ⊗ₜ[F] z)

@[simp] theorem ambientAction_pure (g : Model F) (x y z : NaturalCoordinates.Space F) :
    ambientAction F g (pure F x y z) =
      pure F (NaturalCoordinates.action F g x) (NaturalCoordinates.action F g y)
        (NaturalCoordinates.action F g z) := by
  simp [ambientAction, pure]

/-- The standard coordinate basis on the tensor cube. -/
def ambientBasis : Module.Basis (Fin 6 × Fin 6 × Fin 6) F (Ambient F) :=
  (Pi.basisFun F (Fin 6)).tensorProduct
    ((Pi.basisFun F (Fin 6)).tensorProduct (Pi.basisFun F (Fin 6)))

/-- The 216 actual tensor coordinates, available for root-matrix calculations. -/
def coordinates : Ambient F ≃ₗ[F] ((Fin 6 × Fin 6 × Fin 6) → F) :=
  (ambientBasis F).equivFun

omit [CharP F 2] in
@[simp] theorem coordinates_pure (x y z : NaturalCoordinates.Space F)
    (i j k : Fin 6) : coordinates F (pure F x y z) (i, j, k) = x i * y j * z k := by
  simp [coordinates, ambientBasis, pure, Module.Basis.equivFun_apply, mul_comm, mul_left_comm]

/-- The specified standard natural vectors. -/
def e (i : Fin 6) : NaturalCoordinates.Space F := Pi.single i 1

omit [CharP F 2] in
@[simp] theorem ambientBasis_apply (i j k : Fin 6) :
    ambientBasis F (i, j, k) = pure F (e F i) (e F j) (e F k) := by
  simp [ambientBasis, pure, e, Pi.basisFun_apply]

omit [CharP F 2] in
/-- Every tensor is the sum of its explicitly indexed cube coordinates. -/
theorem sum_coordinates (v : Ambient F) :
    ∑ p : Fin 6 × Fin 6 × Fin 6,
      coordinates F v p • pure F (e F p.1) (e F p.2.1) (e F p.2.2) = v := by
  calc
    _ = ∑ p : Fin 6 × Fin 6 × Fin 6, (ambientBasis F).repr v p • ambientBasis F p := by
      apply Finset.sum_congr rfl
      rintro ⟨i, j, k⟩ _
      rw [ambientBasis_apply]
      rfl
    _ = v := (ambientBasis F).sum_repr v

/-- A coordinate formula for the action on every tensor, hence on the orbit carrier.
Substitution of the six published natural root formulas gives the root matrices. -/
theorem coordinates_ambientAction (g : Model F) (v : Ambient F) (i j k : Fin 6) :
    coordinates F (ambientAction F g v) (i, j, k) =
      ∑ p : Fin 6 × Fin 6 × Fin 6,
        coordinates F v p * (NaturalCoordinates.action F g (e F p.1)) i *
          (NaturalCoordinates.action F g (e F p.2.1)) j *
          (NaturalCoordinates.action F g (e F p.2.2)) k := by
  conv_lhs => rw [← sum_coordinates F v]
  simp only [map_sum, map_smul, ambientAction_pure, Finset.sum_apply, Pi.smul_apply,
    coordinates_pure, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The candidate highest vector in the tensor cube. -/
def seed : Ambient F := pure F (e F 0) (e F 0) (e F 1) +
  pure F (e F 0) (e F 1) (e F 0)

omit [CharP F 2] in
@[simp] theorem coordinates_seed_001 : coordinates F (seed F) (0, 0, 1) = 1 := by
  simp [seed, e]

omit [CharP F 2] in
theorem seed_ne_zero : seed F ≠ 0 := by
  intro h
  have hc := coordinates_seed_001 F
  rw [h, map_zero, Pi.zero_apply] at hc
  exact zero_ne_one hc

private theorem e_zero_fixed (a : F) :
    NaturalCoordinates.action F (rootA a) (e F 0) = e F 0 ∧
    NaturalCoordinates.action F (rootB a) (e F 0) = e F 0 ∧
    NaturalCoordinates.action F (rootC a) (e F 0) = e F 0 ∧
    NaturalCoordinates.action F (rootD a) (e F 0) = e F 0 ∧
    NaturalCoordinates.action F (rootE a) (e F 0) = e F 0 ∧
    NaturalCoordinates.action F (rootF a) (e F 0) = e F 0 :=
  NaturalCoordinates.highestVector_fixed_roots F a

private theorem e_one_fixed (a : F) :
    NaturalCoordinates.action F (rootA a) (e F 1) = e F 1 ∧
    NaturalCoordinates.action F (rootB a) (e F 1) = e F 1 ∧
    NaturalCoordinates.action F (rootC a) (e F 1) = e F 1 ∧
    NaturalCoordinates.action F (rootD a) (e F 1) = e F 1 ∧
    NaturalCoordinates.action F (rootE a) (e F 1) = e F 1 := by
  simp only [action_rootA, action_rootB, action_rootC, action_rootD, action_rootE]
  constructor
  · ext i; fin_cases i <;> simp [e]
  constructor
  · ext i; fin_cases i <;> simp [e]
  constructor
  · ext i; fin_cases i <;> simp [e]
  constructor <;> ext i <;> fin_cases i <;> simp [e]

private theorem e_one_rootF (a : F) :
    NaturalCoordinates.action F (rootF a) (e F 1) = e F 1 + a • e F 0 := by
  ext i; fin_cases i <;> simp [e]

/-- The seed is fixed by all six actual positive root groups. -/
theorem seed_fixed_roots (a : F) :
    ambientAction F (rootA a) (seed F) = seed F ∧
    ambientAction F (rootB a) (seed F) = seed F ∧
    ambientAction F (rootC a) (seed F) = seed F ∧
    ambientAction F (rootD a) (seed F) = seed F ∧
    ambientAction F (rootE a) (seed F) = seed F ∧
    ambientAction F (rootF a) (seed F) = seed F := by
  obtain ⟨hA, hB, hC, hD, hE, hF⟩ := e_zero_fixed F a
  obtain ⟨kA, kB, kC, kD, kE⟩ := e_one_fixed F a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [seed, hA, kA]
  · simp [seed, hB, kB]
  · simp [seed, hC, kC]
  · simp [seed, hD, kD]
  · simp [seed, hE, kE]
  · simp only [seed, map_add, ambientAction_pure, hF, e_one_rootF]
    simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    have hz (v : Ambient F) : v + v = 0 := by
      rw [← two_smul F, (show (2 : F) = 0 from CharP.cast_eq_zero F 2), zero_smul]
    simp [add_left_comm, add_comm, hz]

/-- Torus character of the chosen seed: the sum of the two fundamental weights. -/
theorem seed_torus (l m : Fˣ) :
    ambientAction F (torus l m) (seed F) = ((l : F)^2 * (m : F)) • seed F := by
  have h0 : NaturalCoordinates.action F (torus l m) (e F 0) = (l : F) • e F 0 :=
    NaturalCoordinates.highestVector_torus F l m
  have h1 : NaturalCoordinates.action F (torus l m) (e F 1) = (m : F) • e F 1 := by
    ext i; fin_cases i <;> simp [action_torus, e]
  simp only [seed, map_add, ambientAction_pure, h0, h1]
  simp only [pure, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
    smul_smul, smul_add]
  congr 2 <;> ring

/-- The genuine subrepresentation generated by the specified highest vector. -/
def orbitSpan : Subrepresentation (ambientAction F) where
  toSubmodule := Submodule.span F (Set.range fun g : Model F => ambientAction F g (seed F))
  apply_mem_toSubmodule g := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h, rfl⟩ := hv
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => simp
    | add v w _ _ hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
    | smul a v _ hv => simpa only [map_smul] using Submodule.smul_mem _ a hv

theorem seed_mem_orbitSpan : seed F ∈ orbitSpan F := by
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

/-- The 64 binary positive-unipotent parameters. -/
abbrev BinaryIndex := Fin 6 → Bool

/-- View the binary parameters inside the actual coefficient field. -/
def binaryParameters (t : BinaryIndex) : Fin 6 → F := fun i => if t i then 1 else 0

/-- A word representing the longest Weyl element in the actual G₂ model. -/
def longestWeyl : Model F := (weylR * weylS)^3

/-- The proposed finite basis family consists of 64 actual group translates. -/
def binaryOrbitVector (t : BinaryIndex) : Ambient F :=
  ambientAction F (unipotentProduct (binaryParameters F t) * longestWeyl F) (seed F)

/-- The span of the proposed binary-orbit basis. Its invariance is a separate result. -/
def binarySpan : Submodule F (Ambient F) :=
  Submodule.span F (Set.range (binaryOrbitVector F))

/-- Every member of the finite family belongs to the actual highest-weight orbit span. -/
theorem binaryOrbitVector_mem_orbitSpan (t : BinaryIndex) :
    binaryOrbitVector F t ∈ orbitSpan F :=
  Submodule.subset_span ⟨_, rfl⟩

theorem binarySpan_le_orbitSpan : binarySpan F ≤ (orbitSpan F).toSubmodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  exact binaryOrbitVector_mem_orbitSpan F t

/-- The concrete carrier; dimension and simplicity are separate obligations. -/
abbrev Space := (orbitSpan F).toSubmodule

/-- Restriction of the tensor cube action to the actual generated subspace. -/
def action : Representation F (Model F) (Space F) := (orbitSpan F).toRepresentation

@[simp] theorem action_val (g : Model F) (v : Space F) :
    (action F g v).val = ambientAction F g v.val := rfl

/-- The specified nonzero highest vector in the generated carrier. -/
def highestVector : Space F := ⟨seed F, seed_mem_orbitSpan F⟩

theorem highestVector_ne_zero : highestVector F ≠ 0 := by
  intro h
  exact seed_ne_zero F (congrArg Subtype.val h)

instance : Nontrivial (Space F) := ⟨⟨highestVector F, 0, highestVector_ne_zero F⟩⟩

/-- Its specified highest line; equality with the whole positive fixed space is separate. -/
def highestLine : Submodule F (Space F) := Submodule.span F {highestVector F}

/-- Minimality of the orbit span among actual invariant subspaces. -/
theorem orbitSpan_le_iff (W : Subrepresentation (ambientAction F)) :
    orbitSpan F ≤ W ↔ seed F ∈ W := by
  refine ⟨fun h => h (seed_mem_orbitSpan F), fun h => ?_⟩
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact W.apply_mem_toSubmodule g h

/-- All six positive root subgroups fix the specified highest vector. -/
theorem highestVector_fixed_roots (a : F) :
    action F (rootA a) (highestVector F) = highestVector F ∧
    action F (rootB a) (highestVector F) = highestVector F ∧
    action F (rootC a) (highestVector F) = highestVector F ∧
    action F (rootD a) (highestVector F) = highestVector F ∧
    action F (rootE a) (highestVector F) = highestVector F ∧
    action F (rootF a) (highestVector F) = highestVector F := by
  obtain ⟨hA, hB, hC, hD, hE, hF⟩ := seed_fixed_roots F a
  exact ⟨Subtype.ext hA, Subtype.ext hB, Subtype.ext hC,
    Subtype.ext hD, Subtype.ext hE, Subtype.ext hF⟩

theorem highestVector_fixed_unipotentProduct (t : Fin 6 → F) :
    action F (unipotentProduct t) (highestVector F) = highestVector F := by
  simp only [unipotentProduct, map_mul, Module.End.mul_apply]
  rw [(highestVector_fixed_roots F _).2.2.2.2.2,
    (highestVector_fixed_roots F _).2.2.2.2.1,
    (highestVector_fixed_roots F _).2.2.2.1,
    (highestVector_fixed_roots F _).2.2.1,
    (highestVector_fixed_roots F _).2.1,
    (highestVector_fixed_roots F _).1]

theorem highestVector_torus (l m : Fˣ) :
    action F (torus l m) (highestVector F) = ((l : F)^2 * (m : F)) • highestVector F :=
  Subtype.ext (seed_torus F l m)

/-- Short simple-coroot pairing one. -/
theorem highestVector_shortCoroot (t : Fˣ) :
    action F (shortCoroot t) (highestVector F) = (t : F) • highestVector F := by
  simpa [shortCoroot, pow_two, mul_assoc] using highestVector_torus F t t⁻¹

/-- Long simple-coroot pairing one. -/
theorem highestVector_longCoroot (t : Fˣ) :
    action F (longCoroot t) (highestVector F) = (t : F) • highestVector F := by
  simpa [longCoroot] using highestVector_torus F 1 t

end Atlas.G2.Restricted.Steinberg

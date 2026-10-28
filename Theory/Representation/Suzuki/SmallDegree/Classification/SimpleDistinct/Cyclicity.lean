module

public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct.HighestVector
public import Theory.Representation.G2.TensorClassification.SimpleDistinct.Cyclicity.PairingCriterion

/-!
# Cyclicity of the concrete Suzuki tensor highest vector

The symplectic form `x₀y₃ + x₁y₂ + x₂y₁ + x₃y₀` is invariant under the
literal upper Suzuki root matrices. Entrywise Frobenius preserves the root
subgroup, so tensoring this form and extending scalars gives a root-invariant
pairing on every specified tensor. The actual Weyl matrix reverses the four
coordinates and pairs the highest vector with its translate with value one.

If an orbit span were proper, its right orthogonal complement would contain
a nonzero vector fixed by the root two-group. Highest-line uniqueness would
put the highest vector in that complement, contradicting the pairing value.
Thus uniqueness alone implies cyclicity, over every coefficient extension,
including empty and full support and the parameter `m = 1`.

This supplies the orbit-span premise of
`tensorRep_irreducible_of_fixedLine_and_span`; highest-line uniqueness remains
an independent input. Sources: GLS3, §§2.8.2–2.8.8; Guralnick–Malle,
*Classification of 2F-modules, II*, §3.1, equation (3.2).
-/

open scoped TensorProduct
public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural
set_option backward.isDefEq.respectTransparency false
namespace Cyclicity

private def coordPair (m : ℕ) (i j : Fin 4) : LinearMap.BilinForm (F m) (W m) :=
  (LinearMap.mul (F m) (F m)).compl₁₂ (LinearMap.proj i) (LinearMap.proj j)

/-- The symplectic pairing in the literal four-coordinate convention. -/
def naturalForm (m : ℕ) : LinearMap.BilinForm (F m) (W m) :=
  coordPair m 0 3 + coordPair m 1 2 + coordPair m 2 1 + coordPair m 3 0

/-- Coordinate formula for the natural pairing. -/
theorem naturalForm_apply (m : ℕ) (x y : W m) :
    naturalForm m x y = x 0 * y 3 + x 1 * y 2 + x 2 * y 1 + x 3 * y 0 := by
  rfl

private theorem frobenius_root_mem (m : ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ∈ SuzukiRootSubgroup m) :
    suzukiFieldAutomorphism m g ∈ SuzukiRootSubgroup m := by
  obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m g).mp hg
  apply (mem_suzukiRootSubgroup_iff m _).mpr
  refine ⟨a ^ 2, b ^ 2, ?_⟩
  change Matrix.GeneralLinearGroup.map (frobenius (F m) 2) g.val = _
  rw [hab, map_suzukiRootGL (dvd_refl _)]
  rfl

private theorem frobenius_pow_root_mem (m i : ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ∈ SuzukiRootSubgroup m) :
    (suzukiFieldAutomorphism m ^ i) g ∈ SuzukiRootSubgroup m := by
  induction i with
  | zero => simpa using hg
  | succ i ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact frobenius_root_mem m _ ih

/-- The actual upper root subgroup preserves the natural pairing. -/
theorem naturalForm_invariant (m : ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ∈ SuzukiRootSubgroup m) (x y : W m) :
    naturalForm m (naturalField m g x) (naturalField m g y) = naturalForm m x y := by
  obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m g).mp hg
  have happly (v : W m) (r : Fin 4) :
      naturalField m g v r = ∑ c : Fin 4, (SuzukiRootMatrix m a b) r c * v c := by
    change ∑ c : Fin 4, g.val.val r c * v c = _
    rw [hab]
    rfl
  simp [naturalForm_apply, happly, SuzukiRootMatrix, Fin.sum_univ_four, pow_add]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

/-- Every ordinary Frobenius twist retains root invariance. -/
theorem factorForm_invariant (m i : ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ∈ SuzukiRootSubgroup m) (x y : W m) :
    naturalForm m (factorRep m i g x) (factorRep m i g y) = naturalForm m x y :=
  naturalForm_invariant m _ (frobenius_pow_root_mem m i g hg) x y

/-- The literal reversing Weyl matrix, marked in the Suzuki group. -/
@[expose] def oppositeWeyl (m : ℕ) : SuzukiMatrixGroup m :=
  ⟨SuzukiWeylGL m, Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

/-- Each Frobenius factor pairs highest and opposite highest vectors to one. -/
theorem factorForm_opposite_highestVector (m i : ℕ) :
    naturalForm m (factorRep m i (oppositeWeyl m) (naturalHighestVector m))
      (naturalHighestVector m) = 1 := by
  simp [naturalForm_apply, factorRep_apply, oppositeWeyl, naturalHighestVector,
    SuzukiWeylGL, SuzukiWeylMatrix, Fin.sum_univ_four]

/-- Recursive tensor pairing, with multiplication on the empty tensor word. -/
@[expose] def wordForm (m : ℕ) : (l : List ℕ) → LinearMap.BilinForm (F m) (WordSpace m l)
  | [] => LinearMap.mul (F m) (F m)
  | _ :: l => (naturalForm m).tmul (wordForm m l)

/-- Root invariance of the pairing on an arbitrary tensor word. -/
theorem wordForm_invariant (m : ℕ) (l : List ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ∈ SuzukiRootSubgroup m) (x y : WordSpace m l) :
    wordForm m l (wordRep m l g x) (wordRep m l g y) = wordForm m l x y := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    exact Atlas.G2.TensorClassification.Cyclicity.tensorProductForm_invariant
      (naturalForm m) (wordForm m l) (factorRep m i g) (wordRep m l g)
      (factorForm_invariant m i g hg) ih x y

/-- The same Weyl element yields pairing one at every tensor position. -/
theorem wordForm_opposite_highestVector (m : ℕ) (l : List ℕ) :
    wordForm m l (wordRep m l (oppositeWeyl m) (wordHighestVector m l))
      (wordHighestVector m l) = 1 := by
  induction l with
  | nil => change (1 : F m) * 1 = 1; exact one_mul _
  | cons i l ih =>
    change (naturalForm m).tmul (wordForm m l)
      (factorRep m i (oppositeWeyl m) (naturalHighestVector m) ⊗ₜ[F m]
        wordRep m l (oppositeWeyl m) (wordHighestVector m l))
      (naturalHighestVector m ⊗ₜ[F m] wordHighestVector m l) = 1
    rw [LinearMap.BilinForm.tensorDistrib_tmul, factorForm_opposite_highestVector,
      ih, one_smul]

/-- Scalar extension of the concrete tensor pairing. -/
@[expose] def tensorForm (m : ℕ) (K : Type*) [Field K] [Algebra (F m) K]
    (I : Support m) : LinearMap.BilinForm K (TensorSpace m K I) :=
  (wordForm m (exponents I)).baseChange K

/-- Root invariance survives scalar extension. -/
theorem tensorForm_invariant (m : ℕ) (K : Type*) [Field K] [Algebra (F m) K]
    (I : Support m) (g : SuzukiMatrixGroup m) (hg : g ∈ SuzukiRootSubgroup m)
    (x y : TensorSpace m K I) :
    tensorForm m K I (tensorRep m K I g x) (tensorRep m K I g y) =
      tensorForm m K I x y := by
  have he : (tensorForm m K I).compl₁₂ (tensorRep m K I g) (tensorRep m K I g) =
      tensorForm m K I := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a b
    apply TensorProduct.AlgebraTensorModule.ext
    intro c d
    simp [tensorForm, tensorRep, wordForm_invariant m _ g hg]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

/-- Highest and opposite highest tensors pair to one after scalar extension. -/
theorem tensorForm_opposite_highestVector (m : ℕ) (K : Type*) [Field K]
    [Algebra (F m) K] (I : Support m) :
    tensorForm m K I (tensorRep m K I (oppositeWeyl m) (tensorHighestVector m K I))
      (tensorHighestVector m K I) = 1 := by
  change (wordForm m (exponents I)).baseChange K
    ((1 : K) ⊗ₜ[F m] wordRep m (exponents I) (oppositeWeyl m)
      (wordHighestVector m (exponents I)))
    ((1 : K) ⊗ₜ[F m] wordHighestVector m (exponents I)) = 1
  rw [LinearMap.BilinForm.baseChange_tmul, wordForm_opposite_highestVector]
  simp

end Cyclicity

/-- Highest-line uniqueness implies cyclicity over every coefficient field
extension. No simplicity, algebraic closure, or restriction on support is assumed. -/
theorem tensorHighestVector_orbit_span_of_fixedLine {m : ℕ} {K : Type*}
    [Field K] [Algebra (F m) K] (hm : 1 ≤ m) (I : Support m)
    (hfixed : ∀ v : TensorSpace m K I,
      (∀ g ∈ SuzukiRootSubgroup m, tensorRep m K I g v = v) →
        ∃ c : K, v = c • tensorHighestVector m K I) :
    Submodule.span K (Set.range fun g : SuzukiMatrixGroup m =>
      tensorRep m K I g (tensorHighestVector m K I)) = ⊤ := by
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (F m) K).injective 2
  have hp : IsPGroup (ringChar K) (SuzukiRootSubgroup m) := by
    rw [ringChar.eq K 2]
    exact suzukiRootSubgroup_isPGroup m (by omega)
  apply Atlas.G2.TensorClassification.Cyclicity.orbit_span_eq_top_of_fixedLine_pairing
    (tensorRep m K I) (SuzukiRootSubgroup m) (by rw [ringChar.eq K 2]; decide) hp
    (tensorHighestVector m K I) hfixed (Cyclicity.tensorForm m K I)
    (Cyclicity.tensorForm_invariant m K I) (Cyclicity.oppositeWeyl m)
  rw [Cyclicity.tensorForm_opposite_highestVector]
  exact one_ne_zero

end Representation.SuzukiSmallDegree

end

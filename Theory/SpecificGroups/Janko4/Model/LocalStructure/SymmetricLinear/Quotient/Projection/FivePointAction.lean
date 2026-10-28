module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.Projection.Generators
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Evaluation

/-!
# The genuine five-point action of the literal max4 subgroup

Five explicitly displayed binary row vectors are distinct and permuted by the
two literal ATLAS max4 generators. The ten row identities are kernel-checked
using the existing packed-matrix evaluator. Compatibility with a permutation
is closed under products and inverses and determines the permutation uniquely.
The action therefore extends to the actual subgroup closure.

Source: ATLAS `J4G1-max4W1` and `J4G1-f2r112B0`, attributed in
`SymmetricLinear.Model` and `Janko4.Model.Data`. The five rows are the orbit
`[3,9,11,12,13]` in the saved four-space basis; see `source/README.md`.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.Projection
open Matrix NormalFour.Certificate
open GeneratorCertificates Simplicity.Elevens.BridgeCertificate

private def decodeRow (x : ℕ) : Fin 112 → ZMod 2 := fun j => bit x j.val

private theorem decode_fastRow (x : ℕ) (v : Vector ℕ 112) :
    decodeRow (fastRow x v.toList) = decodeRow x ᵥ* decodeRows v := by
  rw [fastRow_eq]
  funext j
  change bit (packedRow x v) j.val = _
  rw [packedRow, bit_xorList, List.map_ofFn, List.sum_ofFn]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [decodeRow, decodeRows, bit]
  cases h : x.testBit k.val <;> simp [h]

/-- Five packed 112-dimensional rows spanning the invariant four-space. -/
@[expose] def pointRows : Fin 5 → ℕ := ![
  394383704711696877007909874092803,
  2670336318369945608293568049216161,
  1418174137490496686537543451525027,
  971754313872752063926848763433636,
  5087968159279743624923261001571493]

/-- The actual binary row vector represented by a five-point label. -/
@[expose] def point (i : Fin 5) : Fin 112 → ZMod 2 := fun j => bit (pointRows i) j.val

set_option maxRecDepth 10000 in
private lemma first_rows : ∀ i : Fin 5, fastRow (pointRows (firstPerm i)) l028 = pointRows i := by
  decide +kernel

set_option maxRecDepth 10000 in
private lemma second_rows : ∀ i : Fin 5, fastRow (pointRows (secondPerm i)) l025 = pointRows i := by
  decide +kernel

lemma point_injective : Function.Injective point := by decide +kernel

/-- Equivariance with the inverse of the right matrix action. -/
@[expose] def Compatible (g : Model) (s : Equiv.Perm (Fin 5)) : Prop :=
  ∀ i, point (s i) ᵥ* toMatrix g = point i

private lemma first_compatible : Compatible first firstPerm := by
  intro i
  change decodeRow (pointRows (firstPerm i)) ᵥ* toMatrix (first : Model) = _
  rw [show toMatrix (first : Model) = m028 from image_g029]
  change decodeRow (pointRows (firstPerm i)) ᵥ* decodeRows v028 = _
  rw [← decode_fastRow]
  exact congrArg decodeRow (first_rows i)

private lemma second_compatible : Compatible second secondPerm := by
  intro i
  change decodeRow (pointRows (secondPerm i)) ᵥ* toMatrix (second : Model) = _
  rw [show toMatrix (second : Model) = m025 from image_g026]
  change decodeRow (pointRows (secondPerm i)) ᵥ* decodeRows v025 = _
  rw [← decode_fastRow]
  exact congrArg decodeRow (second_rows i)

private lemma compatible_one : Compatible 1 1 := by
  intro i
  simp [map_one]

private lemma compatible_mul {g h : Model} {s t : Equiv.Perm (Fin 5)}
    (hg : Compatible g s) (hh : Compatible h t) : Compatible (g * h) (s * t) := by
  intro i
  rw [map_mul, ← Matrix.vecMul_vecMul, Equiv.Perm.mul_apply, hg, hh]

private lemma compatible_inv {g : Model} {s : Equiv.Perm (Fin 5)}
    (h : Compatible g s) : Compatible g⁻¹ s⁻¹ := by
  intro i
  have hh : point i ᵥ* toMatrix g = point (s⁻¹ i) := by
    simpa using h (s⁻¹ i)
  rw [← hh, Matrix.vecMul_vecMul, ← map_mul, mul_inv_cancel, map_one,
    Matrix.vecMul_one]

private lemma compatible_unique {g : Model} {s t : Equiv.Perm (Fin 5)}
    (hs : Compatible g s) (ht : Compatible g t) : s = t := by
  apply Equiv.ext
  intro i
  apply point_injective
  have h := congrArg (fun v => v ᵥ* toMatrix g⁻¹) ((hs i).trans (ht i).symm)
  simpa only [Matrix.vecMul_vecMul, ← map_mul, mul_inv_cancel, map_one,
    Matrix.vecMul_one] using h

private def liftGroup : Subgroup Model where
  carrier := {g | ∃ s, Compatible g s}
  one_mem' := ⟨1, compatible_one⟩
  mul_mem' := by
    rintro g h ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s * t, compatible_mul hs ht⟩
  inv_mem' := by
    rintro g ⟨s, hs⟩
    exact ⟨s⁻¹, compatible_inv hs⟩

private lemma max4_le_liftGroup : max4Subgroup ≤ liftGroup := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | rfl
  · exact ⟨firstPerm, first_compatible⟩
  · exact ⟨secondPerm, second_compatible⟩

private lemma exists_perm (g : max4Subgroup) : ∃ s, Compatible g s := max4_le_liftGroup g.property

/-- The action of the literal max4 subgroup on five distinct binary rows. -/
noncomputable def fivePointHom : max4Subgroup →* Equiv.Perm (Fin 5) where
  toFun g := Classical.choose (exists_perm g)
  map_one' := compatible_unique (Classical.choose_spec (exists_perm 1)) compatible_one
  map_mul' g h := compatible_unique (Classical.choose_spec (exists_perm (g * h)))
    (compatible_mul (Classical.choose_spec (exists_perm g))
      (Classical.choose_spec (exists_perm h)))

lemma fivePointHom_spec (g : max4Subgroup) : Compatible g (fivePointHom g) :=
  Classical.choose_spec (exists_perm g)

lemma fivePointHom_first : fivePointHom first = firstPerm :=
  compatible_unique (fivePointHom_spec _) first_compatible

lemma fivePointHom_second : fivePointHom second = secondPerm :=
  compatible_unique (fivePointHom_spec _) second_compatible

end Janko4.LocalStructure.SymmetricLinear.Projection

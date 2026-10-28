module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.Construction

/-!
# Coefficient embeddings and Ree fixed points

Every homomorphism of coefficient fields acts entrywise on the integral F4
root matrices. The action commutes with the exceptional endomorphism, since
its root formula uses only the root permutation and squaring. If the smaller
odd degree divides the larger, this gives an injective homomorphism of the
full Ree groups, whose image lies in the smaller exceptional fixed group.
The proof includes parameter zero.

Source: the root-generated construction in Steinberg, *Lectures on Chevalley
Groups*, and the subfield groups in Malle, J. Algebra 139 (1991), 52–69.
-/

@[expose] public section

namespace ReeF4.Subfield

open Theory.AlgebraicGroup
open RootPairing.IntegralGeckConstruction

noncomputable section

/-- Divisibility of the field degrees supplies an actual coefficient embedding. -/
theorem nonempty_coefficientHom {k m : ℕ}
    (hdiv : (2 * k + 1) ∣ (2 * m + 1)) :
    Nonempty (CoefficientField k →+* CoefficientField m) := by
  have h : Module.finrank (ZMod 2) (CoefficientField k) ∣
      Module.finrank (ZMod 2) (CoefficientField m) := by
    simpa only [GaloisField.finrank 2 (by omega : 2 * k + 1 ≠ 0),
      GaloisField.finrank 2 (by omega : 2 * m + 1 ≠ 0)] using hdiv
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd h
  exact ⟨f.toRingHom⟩

/-- Entrywise application of a coefficient embedding to matrix units. -/
def unitsMap {k m : ℕ} (f : CoefficientField k →+* CoefficientField m) :
    MatrixUnits k →* MatrixUnits m := Units.map f.mapMatrix.toMonoidHom

theorem unitsMap_rootCurve {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m)
    (r : F4Chevalley.Root) (t : CoefficientField k) :
    unitsMap f (F4Chevalley.rootCurve r t) = F4Chevalley.rootCurve r (f t) := by
  apply Units.ext
  change (↑(F4Chevalley.rootCurve r t) : MatrixCarrier k).map f = _
  rw [F4Chevalley.rootCurve_matrix_formula, F4Chevalley.rootCurve_matrix_formula]
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    specializeMatrix, Matrix.one_apply, apply_ite f]

theorem unitsMap_mem {k m : ℕ} (f : CoefficientField k →+* CoefficientField m)
    {x : MatrixUnits k} (hx : x ∈ SplitGroup k) : unitsMap f x ∈ SplitGroup m := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨⟨r, t⟩, rfl⟩
      simpa only [rootGenerator_apply, unitsMap_rootCurve] using
        rootGenerator_mem m (r, f t)
  | one => simp
  | mul x y _ _ hx hy => simpa only [map_mul] using (SplitGroup m).mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using (SplitGroup m).inv_mem hx

/-- The coefficient embedding restricted to the actual split F4 groups. -/
def splitMap {k m : ℕ} (f : CoefficientField k →+* CoefficientField m) :
    SplitGroup k →* SplitGroup m :=
  ((unitsMap f).comp (SplitGroup k).subtype).codRestrict (SplitGroup m)
    (fun x => unitsMap_mem f x.property)

@[simp] theorem splitMap_rootGenerator {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m)
    (r : F4Chevalley.Root) (t : CoefficientField k) :
    splitMap f (rootGeneratorInGroup k r t) = rootGeneratorInGroup m r (f t) := by
  apply Subtype.ext
  exact unitsMap_rootCurve f r t

theorem splitMap_injective {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) : Function.Injective (splitMap f) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply f.injective
  exact congrArg (fun z : SplitGroup m => (z.val : MatrixCarrier m) i j) h

/-- The exceptional root substitution is natural in the coefficient field. -/
theorem splitMap_exceptional {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) (x : SplitGroup k) :
    splitMap f (exceptionalEndomorphism k x) = exceptionalEndomorphism m (splitMap f x) := by
  have h : (splitMap f).comp (exceptionalEndomorphism k) =
      (exceptionalEndomorphism m).comp (splitMap f) := by
    apply splitGroup_hom_ext (m := k)
    intro r t
    change splitMap f (exceptionalEndomorphism k (rootGeneratorInGroup k r t)) =
      exceptionalEndomorphism m (splitMap f (rootGeneratorInGroup k r t))
    simp only [exceptionalEndomorphism_rootGenerator,
      splitMap_rootGenerator]
    congr 1
    classical
    by_cases hr : IsLongRoot r
    · rw [exceptionalParameter_of_long hr, exceptionalParameter_of_long hr]
    · rw [exceptionalParameter_of_short hr, exceptionalParameter_of_short hr, map_pow]
  exact DFunLike.congr_fun h x

theorem splitMap_exceptional_pow {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) (n : ℕ) (x : SplitGroup k) :
    splitMap f ((exceptionalEndomorphism k ^ n) x) =
      (exceptionalEndomorphism m ^ n) (splitMap f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change splitMap f (exceptionalEndomorphism k ((exceptionalEndomorphism k ^ n) x)) =
        exceptionalEndomorphism m ((exceptionalEndomorphism m ^ n) (splitMap f x))
      rw [splitMap_exceptional, ih]

/-- Smaller Ree fixed points remain fixed by the corresponding exceptional
power after the coefficient embedding. -/
theorem splitMap_fixed {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) (x : Model k) :
    (exceptionalEndomorphism m ^ (2 * k + 1)) (splitMap f (toSplitGroup k x)) =
      splitMap f (toSplitGroup k x) := by
  rw [← splitMap_exceptional_pow]
  rw [← reeTwist_eq_pow, reeTwist_toSplitGroup]

/-- The actual embedding of full Ree groups for an inclusion of odd field degrees. -/
def reeMap {k m : ℕ} (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (f : CoefficientField k →+* CoefficientField m) : Model k →* Model m :=
  ((splitMap f).comp (toSplitGroup k)).codRestrict (fixedSubgroup m) (by
    intro x
    rw [mem_fixedSubgroup, reeTwist_eq_pow]
    obtain ⟨a, ha⟩ := hdiv
    have hp : exceptionalEndomorphism m ^ (2 * m + 1) =
        (exceptionalEndomorphism m ^ (2 * k + 1)) ^ a :=
      (congrArg (fun n => exceptionalEndomorphism m ^ n) ha).trans (pow_mul _ _ _)
    rw [hp]
    exact pow_apply_eq_of_apply_eq _ (splitMap_fixed f x) a)

@[simp] theorem toSplitGroup_reeMap {k m : ℕ}
    (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (f : CoefficientField k →+* CoefficientField m) (x : Model k) :
    toSplitGroup m (reeMap hdiv f x) = splitMap f (toSplitGroup k x) := by
  rw [toSplitGroup_apply]
  rfl

theorem reeMap_injective {k m : ℕ} (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (f : CoefficientField k →+* CoefficientField m) : Function.Injective (reeMap hdiv f) := by
  intro x y h
  apply toSplitGroup_injective k
  apply splitMap_injective f
  simpa only [toSplitGroup_reeMap] using congrArg (toSplitGroup m) h

/-- The embedding lands in the intrinsic smaller fixed group. Equality of
this range and the whole fixed group is the remaining descent calculation. -/
theorem reeMap_range_le {k m : ℕ} (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (f : CoefficientField k →+* CoefficientField m) :
    (reeMap hdiv f).range ≤ fixedSubfield m k := by
  rintro _ ⟨x, rfl⟩
  rw [mem_fixedSubfield, toSplitGroup_reeMap]
  exact splitMap_fixed f x

/-- A smaller exceptional fixed point has entries in the corresponding
Frobenius fixed field. This is the coefficient part of field descent. -/
theorem entry_pow_eq_of_mem_fixedSubfield {m k : ℕ} {x : Model m}
    (hx : x ∈ fixedSubfield m k) (i j : F4Chevalley.BasisIndex) :
    ((toSplitGroup m x).val : MatrixCarrier m) i j ^ (2 ^ (2 * k + 1)) =
      ((toSplitGroup m x).val : MatrixCarrier m) i j := by
  have h := pow_apply_eq_of_apply_eq
    (exceptionalEndomorphism m ^ (2 * k + 1)) hx 2
  rw [← pow_mul, Nat.mul_comm (2 * k + 1) 2, pow_mul,
    exceptionalEndomorphism_sq] at h
  have he := congrArg (fun z : SplitGroup m => (z.val : MatrixCarrier m) i j) h
  rwa [splitFrobenius_pow_entry] at he

end

end ReeF4.Subfield

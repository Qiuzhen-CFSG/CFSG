module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.Data
/-!
# Two possible images of the shear

Three relations suffice: u²=1, (uj)³=1 and (ut)³=1, where j is the flip
and t=diag(ω,ω⁻¹). Among the sixty determinant-one matrices over GF(4),
only the upper and lower shears satisfy the transported relations with
j and t⁻¹. The finite check is performed in the kernel over `GoldenFour`,
then transported through an actual field isomorphism to the coordinate field.

Applied to `Data.twist`, this proves the precise alternatives needed for
the ambient exclusion in `DiagonalSelection`. It makes no uniqueness claim
from the common S₃ alone. Source: Aschbacher, *Sporadic Groups* (1994),
Lemma 49.5, p.284, with that local inference repaired by the ambient order.
-/

open Matrix Atlas.Algebra
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.DiagonalSelection
@[expose] public section
variable {R S : Type*} [Field R] [Field S] [CharP R 2] [CharP S 2]
def lowerShear : SL(2,R) := ⟨!![1,0;1,1], by simp [Matrix.det_fin_two]⟩

omit [CharP R 2] [CharP S 2] in
theorem slMap_injective {n : ℕ} (e : R →+* S) (he : Function.Injective e) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin n) e) := by
  intro x y h
  apply Subtype.ext
  ext i j
  exact he (congrArg (fun a : SL(n,S) => a.val i j) h)

@[simp] theorem slMap_flip (e : R →+* S) :
    Matrix.SpecialLinearGroup.map e (flip (K := R)) = flip := by
  apply Subtype.ext
  change (flip (K := R)).val.map e = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, flip]

omit [CharP R 2] [CharP S 2] in
@[simp] theorem slMap_shear (e : R →+* S) :
    Matrix.SpecialLinearGroup.map e (shear (K := R)) = shear := by
  apply Subtype.ext
  change (shear (K := R)).val.map e = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, shear]

omit [CharP R 2] [CharP S 2] in
@[simp] theorem slMap_lower (e : R →+* S) :
    Matrix.SpecialLinearGroup.map e (lowerShear (R := R)) = lowerShear := by
  apply Subtype.ext
  change (lowerShear (R := R)).val.map e = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, lowerShear]

omit [CharP R 2] [CharP S 2] in
@[simp] theorem slMap_torus (e : R →+* S) (t : Rˣ) :
    Matrix.SpecialLinearGroup.map e (torus t) = torus (Units.map e t) := by
  apply Subtype.ext
  change (torus t).val.map e = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, torus]

abbrev K := GoldenFour
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def cubicUnit : Kˣ := ⟨goldenFourTau, 1+goldenFourTau, by decide +kernel, by decide +kernel⟩
def cubic : SL(2,K) := torus cubicUnit

theorem shear_relations : (shear (K := K)) ^ 2 = 1 ∧
    (shear * flip (K := K))^3 = 1 ∧ (shear * cubic)^3 = 1 := by decide +kernel

theorem shear_alternatives : ∀ a : SL(2,K), a^2 = 1 → (a*flip)^3 = 1 →
    (a*cubic⁻¹)^3 = 1 → a = shear ∨ a = lowerShear := by decide +kernel

theorem hom_shear_alternatives (f : SL(2,K) →* SL(2,K))
    (hf : f flip = flip) (ht : f cubic = cubic⁻¹) :
    f shear = shear ∨ f shear = lowerShear := by
  apply shear_alternatives
  · simpa only [map_pow, map_one] using congrArg f shear_relations.1
  · simpa only [map_pow, map_mul, map_one, hf] using congrArg f shear_relations.2.1
  · simpa only [map_pow, map_mul, map_one, ht] using congrArg f shear_relations.2.2

noncomputable def fieldEquiv : K ≃+* F := by
  letI : Fintype F := Fintype.ofFinite F
  exact FiniteField.ringEquivOfCardEq (by
    rw [goldenFour_card, ← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
    norm_num)

theorem data_shear_alternatives {L : LongFrame} (D : Data L) :
    D.twist shear = shear ∨ D.twist shear = lowerShear := by
  let toK := Matrix.SpecialLinearGroup.map (n := Fin 2) fieldEquiv.symm.toRingHom
  let toF := Matrix.SpecialLinearGroup.map (n := Fin 2) fieldEquiv.toRingHom
  let f := toK.comp (D.twist.toMonoidHom.comp toF)
  have hf : f flip = flip := by
    simp [f, toF, toK, D.twist_flip]
  have ht : f cubic = cubic⁻¹ := by
    change toK (D.twist (toF (torus cubicUnit))) = _
    rw [show toF (torus cubicUnit) = torus (Units.map fieldEquiv.toRingHom cubicUnit) from
      slMap_torus _ _]
    rw [D.twist_torus, ← slMap_torus]
    rw [map_inv]
    congr 1
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    exact fieldEquiv.symm_apply_apply _
  have h := hom_shear_alternatives f hf ht
  have hinj := slMap_injective (n := 2) fieldEquiv.symm.toRingHom fieldEquiv.symm.injective
  change toK (D.twist (toF shear)) = shear ∨
    toK (D.twist (toF shear)) = lowerShear at h
  rw [show toF shear = shear from slMap_shear _] at h
  rcases h with h | h
  · exact Or.inl (hinj (h.trans (slMap_shear _).symm))
  · exact Or.inr (hinj (h.trans (slMap_lower _).symm))
end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.DiagonalSelection

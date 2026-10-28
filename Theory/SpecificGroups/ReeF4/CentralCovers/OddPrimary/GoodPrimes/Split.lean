module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.TorusTransfer
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation

/-!
# The rational product torus in the Ree group

For `q = 2^(2*m+1)` and `m ≥ 1`, the concrete full linear Levi is
`SL₂(GF(q)) × GF(q)ˣ`. Its isomorphism is constructed from the two commuting
end-node root representations exchanged by the exceptional twist, together
with the complementary diagonal torus. We use its inverse followed by the
literal subgroup inclusion into `Model m`.

The diagonal matrices `diag(a,a⁻¹)` and the complementary unit factor give
an injective product torus. The Weyl matrix `!![0,1;1,0]` in the first factor
inverts the first coordinate and commutes with the second. Transporting that
matrix through the same Levi inclusion gives one actual Ree element realizing
`ReversesPair` for every parameter. Cyclic coordinates on the field units
then give `ProductTorusEmbedding m (q-1)`.

This discharges the split embedding premise of the good-prime torus transfer;
the order and index calculations remain in its parent application.
Sources: GLS3 §§2.2–2.4, Example 2.6.3 and Theorem 2.6.5(f,g),
`refs/KGroup/GLS3/chapter2.tex`, and §4.10 in `chapter4.tex`.
This is the rational-torus input to the Ree central-cover calculation for
Aschbacher–Smith I.1.1–4, printed pp.407–408 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace ReeF4.CentralCovers.OddPrimary.Split
open Matrix
open ConverseParabolics

private def diagonalHom (m : ℕ) :
    (CoefficientField m)ˣ →* SpecialLinearGroup (Fin 2) (CoefficientField m) where
  toFun a := SpecialLinearGroup.diag2 (a : CoefficientField m) a.ne_zero
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.diag2_coe']
  map_mul' a b := by
    apply Subtype.ext
    change _ = (SpecialLinearGroup.diag2 (a : CoefficientField m) a.ne_zero).val *
      (SpecialLinearGroup.diag2 (b : CoefficientField m) b.ne_zero).val
    simp only [SpecialLinearGroup.diag2_coe']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem diagonalHom_injective (m : ℕ) : Function.Injective (diagonalHom m) := by
  intro a b h
  apply Units.ext
  have he := congrArg (fun A : SpecialLinearGroup (Fin 2) (CoefficientField m) => A.val 0 0) h
  change (a : CoefficientField m) = (b : CoefficientField m) at he
  exact he

private def weyl (m : ℕ) : SpecialLinearGroup (Fin 2) (CoefficientField m) :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private theorem weyl_diagonal (m : ℕ) (a : (CoefficientField m)ˣ) :
    weyl m * diagonalHom m a = diagonalHom m a⁻¹ * weyl m := by
  apply Subtype.ext
  change (weyl m).val * (SpecialLinearGroup.diag2 (a : CoefficientField m) a.ne_zero).val =
    (SpecialLinearGroup.diag2 (↑a⁻¹ : CoefficientField m) (Units.ne_zero a⁻¹)).val * (weyl m).val
  simp only [SpecialLinearGroup.diag2_coe']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, Matrix.mul_apply, Fin.sum_univ_two]

/-- Inclusion through the concrete root-constructed full linear Levi. -/
def leviHom {m : ℕ} (hm : 1 ≤ m) :
    SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ →* Model m :=
  (SectionGeometry.LinearRadical.fullLevi m).subtype.comp
    (linearFullLeviEquiv hm).symm.toMonoidHom

theorem leviHom_injective {m : ℕ} (hm : 1 ≤ m) : Function.Injective (leviHom hm) :=
  Subtype.val_injective.comp (linearFullLeviEquiv hm).symm.injective

/-- The split product torus, in internal and complementary Levi coordinates. -/
def unitTorusHom {m : ℕ} (hm : 1 ≤ m) :
    (CoefficientField m)ˣ × (CoefficientField m)ˣ →* Model m :=
  (leviHom hm).comp ((diagonalHom m).prodMap (MonoidHom.id _))

theorem unitTorusHom_injective {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (unitTorusHom hm) := by
  intro a b hab
  have h := leviHom_injective hm hab
  change (diagonalHom m a.1, a.2) = (diagonalHom m b.1, b.2) at h
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  exact Prod.ext (diagonalHom_injective m h₁) h₂

/-- The Weyl element in the actual fixed group, with trivial complementary coordinate. -/
def inverter {m : ℕ} (hm : 1 ≤ m) : Model m := leviHom hm (weyl m, 1)

theorem inverter_first {m : ℕ} (hm : 1 ≤ m) (a : (CoefficientField m)ˣ) :
    inverter hm * unitTorusHom hm (a, 1) * (inverter hm)⁻¹ =
      (unitTorusHom hm (a, 1))⁻¹ := by
  change leviHom hm (weyl m, 1) * leviHom hm (diagonalHom m a, 1) *
    (leviHom hm (weyl m, 1))⁻¹ = (leviHom hm (diagonalHom m a, 1))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
  congr 1
  apply Prod.ext
  · change weyl m * diagonalHom m a * (weyl m)⁻¹ = (diagonalHom m a)⁻¹
    rw [weyl_diagonal, mul_inv_cancel_right, map_inv]
  · simp

theorem inverter_second {m : ℕ} (hm : 1 ≤ m) (a : (CoefficientField m)ˣ) :
    Commute (inverter hm) (unitTorusHom hm (1, a)) := by
  change Commute (leviHom hm (weyl m, 1)) (leviHom hm (diagonalHom m 1, a))
  rw [map_one]
  apply Commute.map
  show (weyl m, (1 : (CoefficientField m)ˣ)) * (1, a) = (1, a) * (weyl m, 1)
  simp

theorem unitTorusHom_reverses {m : ℕ} (hm : 1 ≤ m) (a : (CoefficientField m)ˣ) :
    ReversesPair (unitTorusHom hm (a, 1)) (unitTorusHom hm (1, a)) :=
  Or.inr ⟨inverter hm, inverter_first hm a, inverter_second hm a⟩

/-- Cyclic coordinates of the coefficient-field units. -/
def cyclicEquiv (m : ℕ) :
    Multiplicative (ZMod (2 ^ (2 * m + 1) - 1)) ≃* (CoefficientField m)ˣ := by
  have hcard : Nat.card (CoefficientField m)ˣ = 2 ^ (2 * m + 1) - 1 := by
    rw [Nat.card_units, field_card]
  rw [← hcard]
  exact zmodCyclicMulEquiv (inferInstance : IsCyclic (CoefficientField m)ˣ)

/-- The marked rational product torus with its ambient partial inverter. -/
def embedding {m : ℕ} (hm : 1 ≤ m) : ProductTorusEmbedding m (2 ^ (2 * m + 1) - 1) := by
  let e := (cyclicEquiv m).toMonoidHom
  refine ⟨(unitTorusHom hm).comp (e.prodMap e), ?_, ?_⟩
  · intro a b hab
    have h := unitTorusHom_injective hm hab
    change (e a.1, e a.2) = (e b.1, e b.2) at h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    exact Prod.ext ((cyclicEquiv m).injective h₁) ((cyclicEquiv m).injective h₂)
  · intro z
    change ReversesPair (unitTorusHom hm (e z, e 1)) (unitTorusHom hm (e 1, e z))
    rw [map_one]
    exact unitTorusHom_reverses hm (e z)

end ReeF4.CentralCovers.OddPrimary.Split

namespace ReeF4.CentralCovers.OddPrimary

/-- The rational Ree product torus, including its actual ambient pair action. -/
theorem nonempty_split_productTorusEmbedding (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) - 1)) :=
  ⟨Split.embedding hm⟩

end ReeF4.CentralCovers.OddPrimary

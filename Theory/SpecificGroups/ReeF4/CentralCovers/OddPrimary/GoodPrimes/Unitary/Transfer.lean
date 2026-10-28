module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.TorusTransfer
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Model
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.SingerParameters

/-!
# Full unitary torus coordinates and their Ree applications

The full norm-one subgroup over GF(q²) is cyclic of order q+1. Two copies
map injectively to diag(a,(ab)⁻¹,b) in SU₃. In characteristic two the
first/last coordinate transposition has determinant one and exchanges the
two coordinates. An injective map of this monomial matrix group into Ree
therefore supplies the literal `ProductTorusEmbedding`, with Ree conjugators.

For the Singer factor, a faithful action of the explicit GF(q⁶) parameters
on the identity Hermitian three-space gives a cyclic SU₃ subgroup of order
q²−q+1. A full-SU₃ embedding into the literal exceptional fixed group then
supplies both requested torus embeddings. Both construction inputs remain
explicit; no existence theorem for exceptional descent is asserted here.
The product also consumes the existing monomial descent independently of
its ambient inverter or its three-primary Sylow deductions.

Sources: GLS3 Example 2.6.3, Table 4.7.3A and §4.10, in
refs/KGroup/GLS3/chapter2.tex and chapter4.tex. Example 2.6.3 uses the
half-integer Ree parameter, whose square is q here. The table specifies
universal SU₃, retaining its scalar center of order three.
-/

@[expose] public noncomputable section

namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary
open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary

variable {F : Type*} [Field F] [CharP F 2]
    (J : HermitianForm 3 F) (hJ : J.form = 1)

/-- The full norm-one diagonal map is injective before projectivization. -/
theorem normDiagonal_injective : Function.Injective (Three.Unitary.normDiagonal J hJ) := by
  intro a b he
  have he' := congrArg (fun x : Three.Unitary.monomial J hJ => x.val.val.val) he
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    exact congrArg (fun A => A 0 0) he'
  · apply Subtype.ext
    apply Units.ext
    exact congrArg (fun A => A 2 2) he'

/-- The coordinate transposition exchanges the full norm-one coordinates. -/
theorem swap_normDiagonal (a : HermitianForm.EvenInner.normOne J ×
    HermitianForm.EvenInner.normOne J) :
    Three.Unitary.swap J hJ * Three.Unitary.normDiagonal J hJ a *
      (Three.Unitary.swap J hJ)⁻¹ = Three.Unitary.normDiagonal J hJ (a.2, a.1) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Three.Unitary.swap, Three.Unitary.swapSU, Three.Unitary.normDiagonal,
      MatrixTorus.diagonalSpecial, MatrixTorus.diagonalGL_val, MatrixTorus.entries,
      MatrixTorus.swapGL, Matrix.mul_apply, Fin.sum_univ_succ, mul_assoc, mul_comm]

/-- The full cyclic parameter group, retaining its scalar three-part. -/
def normOneEquiv (m : ℕ) : Multiplicative (ZMod (2 ^ (2 * m + 1) + 1)) ≃*
    HermitianForm.EvenInner.normOne (Three.form m) :=
  mulEquivOfCyclicCardEq (by
    change Nat.card (ZMod _) = _
    rw [Nat.card_zmod, HermitianForm.EvenInner.normOne_card (Three.form m)
      (Three.quadraticField_card m) (Three.form_conj m)])

/-- A full product of the specified cyclic groups in the concrete monomial SU₃. -/
def monomialProduct (m : ℕ) :
    Multiplicative (ZMod (2 ^ (2 * m + 1) + 1)) ×
      Multiplicative (ZMod (2 ^ (2 * m + 1) + 1)) →* Three.MonomialGroup m :=
  (Three.Unitary.normDiagonal (Three.form m) (Three.form_matrix m)).comp
    ((normOneEquiv m).prodCongr (normOneEquiv m)).toMonoidHom

theorem monomialProduct_injective (m : ℕ) : Function.Injective (monomialProduct m) :=
  (normDiagonal_injective (Three.form m) (Three.form_matrix m)).comp
    ((normOneEquiv m).prodCongr (normOneEquiv m)).injective

/-- Swapping the specified cyclic coordinates uses an actual SU₃ matrix. -/
theorem swap_monomialProduct (m : ℕ)
    (a : Multiplicative (ZMod (2 ^ (2 * m + 1) + 1)) ×
      Multiplicative (ZMod (2 ^ (2 * m + 1) + 1))) :
    Three.Unitary.swap (Three.form m) (Three.form_matrix m) * monomialProduct m a *
      (Three.Unitary.swap (Three.form m) (Three.form_matrix m))⁻¹ =
        monomialProduct m (a.2, a.1) :=
  swap_normDiagonal (Three.form m) (Three.form_matrix m) _

/-- Any actual monomial descent gives the required full product torus in Ree.
The inverter and three-primary Sylow conclusion are not prerequisites. -/
def productTorusEmbedding {m : ℕ} (j : Three.MonomialGroup m →* Model m)
    (hj : Function.Injective j) : ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1) where
  map := j.comp (monomialProduct m)
  injective := hj.comp (monomialProduct_injective m)
  reverses z := by
    apply Or.inl
    refine ⟨j (Three.Unitary.swap (Three.form m) (Three.form_matrix m)), ?_, ?_⟩
    · simpa only [map_mul, map_inv, MonoidHom.comp_apply] using congrArg j (swap_monomialProduct m (z, 1))
    · simpa only [map_mul, map_inv, MonoidHom.comp_apply] using congrArg j (swap_monomialProduct m (1, z))

/-- Direct application to the existing three-primary producer's stronger descent. -/
theorem nonempty_product_of_monomialRealization {m : ℕ}
    (D : Three.MonomialRealization m) :
    Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1)) :=
  ⟨productTorusEmbedding D.embedding D.injective⟩

/-- Restrict an injective full-SU₃ map to obtain the product torus and its swap. -/
def productTorusEmbeddingOfSpecial {m : ℕ}
    (j : (Three.form m).specialSubgroup →* Model m) (hj : Function.Injective j) :
    ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1) :=
  productTorusEmbedding (j.comp (Three.MonomialGroup m).subtype)
    (hj.comp (Three.MonomialGroup m).subtype_injective)

/-- A cyclic subgroup of full SU₃ of the Singer order yields the literal cyclic
embedding in Ree, with no division by the scalar three-center. -/
def cyclicTorusEmbeddingOfSpecial {m : ℕ}
    (j : (Three.form m).specialSubgroup →* Model m) (hj : Function.Injective j)
    (T : Subgroup (Three.form m).specialSubgroup) [IsCyclic T]
    (hT : Nat.card T = (2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1) :
    CyclicTorusEmbedding m ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1) := by
  let e : Multiplicative (ZMod ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1)) ≃* T :=
    mulEquivOfCyclicCardEq (by change Nat.card (ZMod _) = _; rw [Nat.card_zmod, hT])
  exact ⟨j.comp (T.subtype.comp e.toMonoidHom), hj.comp (T.subtype_injective.comp e.injective)⟩

/-- Assembly of both requested tori from the independent full-SU₃ descent and
Singer construction. Neither construction premise is asserted in this module. -/
theorem nonempty_tori_of_special {m : ℕ}
    (j : (Three.form m).specialSubgroup →* Model m) (hj : Function.Injective j)
    (hSinger : ∃ T : Subgroup (Three.form m).specialSubgroup,
      IsCyclic T ∧ Nat.card T = (2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1) :
    Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1)) ∧
      Nonempty (CyclicTorusEmbedding m ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1)) := by
  obtain ⟨T, hcyc, hT⟩ := hSinger
  let := hcyc
  exact ⟨⟨productTorusEmbeddingOfSpecial j hj⟩, ⟨cyclicTorusEmbeddingOfSpecial j hj T hT⟩⟩

/-- A faithful unitary action of the explicit field parameters gives a cyclic
special-unitary subgroup with its full order. -/
theorem singer_subgroup_of_parameters {m : ℕ}
    (f : SingerParameters.Group m →* (Three.form m).specialSubgroup)
    (hf : Function.Injective f) :
    ∃ T : Subgroup (Three.form m).specialSubgroup,
      IsCyclic T ∧ Nat.card T = SingerParameters.order m := by
  refine ⟨f.range, ?_, ?_⟩
  · exact isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  · exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans
      (SingerParameters.card m)

/-- The exact two Ree outputs from independent descent and trace-form actions. -/
theorem nonempty_tori_of_parameter_embedding {m : ℕ}
    (j : (Three.form m).specialSubgroup →* Model m) (hj : Function.Injective j)
    (f : SingerParameters.Group m →* (Three.form m).specialSubgroup)
    (hf : Function.Injective f) :
    Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1)) ∧
      Nonempty (CyclicTorusEmbedding m ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1)) :=
  nonempty_tori_of_special j hj (singer_subgroup_of_parameters f hf)

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary

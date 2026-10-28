module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Transfer
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Data
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.FixedModel
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Faithful full unitary descent from the split A₂ × A₂ construction

The literal identity-form SU₃ over GF(q²), q = 2^(2m + 1), maps to the
unitary graph in the two SL₃ factors. Its intersection with the diagonal
cubic kernel is trivial, preserving the scalar center of order three.
The subsystem twist equation then fixes this image after conjugation by a
Lang solution. The proved rational-descent equivalence sends it into the
actual root-generated finite Ree group. `intoModel_coefficient_image`
records the original coefficient-extension map, so this comparison does
not use an assumed model equivalence.

The split subsystem construction remains an explicit `SubsystemData` input.
No unconditional SU₃ embedding is asserted until that input is constructed.
Both field embeddings, Lang solvability, and rational descent are discharged
in `exists_embedding_of_subsystem`. The final theorem applies
`productTorusEmbeddingOfSpecial` to this full unitary map.

Sources: GLS3 Example 2.6.3 and Table 4.7.3A in
`refs/KGroup/GLS3/chapter2.tex` and `chapter4.tex`, with the source's
half-integer Ree parameter having square q. Rational descent uses Steinberg,
*Lectures on Chevalley Groups*, Theorem 7 and its third corollary.
-/

@[expose] public noncomputable section

namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent
open ReeF4.CentralCovers.OddPrimary.Cyclotomic

variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

def SubsystemData.unitaryMap {m : ℕ} (D : SubsystemData m F)
    (f : Three.QuadraticField m →+* F) :
    (Three.form m).specialSubgroup →* AlgebraicPoints F :=
  D.map.comp (unitaryPair m f)

theorem SubsystemData.unitaryMap_injective {m : ℕ} (D : SubsystemData m F)
    (f : Three.QuadraticField m →+* F) : Function.Injective (D.unitaryMap f) :=
  (graphPair_injective_mod_diagonalCenter m D.map D.kernel).comp (unitarySL_injective m f)

theorem SubsystemData.unitaryMap_twisted {m : ℕ} (D : SubsystemData m F)
    (f : Three.QuadraticField m →+* F) (x : (Three.form m).specialSubgroup) :
    D.weyl * (algebraicReeTwist m).onPoints (D.unitaryMap f x) * D.weyl⁻¹ =
      D.unitaryMap f x := by
  change D.weyl * (algebraicReeTwist m).onPoints (D.map (unitaryPair m f x)) * D.weyl⁻¹ = _
  rw [D.intertwines, unitaryPair_fixed]
  rfl

def SubsystemData.intoFixed {m : ℕ} (D : SubsystemData m F)
    (f : Three.QuadraticField m →+* F) (g : AlgebraicPoints F)
    (hg : g * ((algebraicReeTwist m).onPoints g)⁻¹ = D.weyl) :
    (Three.form m).specialSubgroup →* algebraicFixed (algebraicReeTwist (F := F) m).onPoints :=
  (((MulAut.conj g⁻¹).toMonoidHom).comp (D.unitaryMap f)).codRestrict _ (fun x => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact conjugated_fixed _ D.weyl g _ hg (D.unitaryMap_twisted f x))

theorem SubsystemData.intoFixed_injective {m : ℕ} (D : SubsystemData m F)
    (f : Three.QuadraticField m →+* F) (g : AlgebraicPoints F)
    (hg : g * ((algebraicReeTwist m).onPoints g)⁻¹ = D.weyl) :
    Function.Injective (D.intoFixed f g hg) := by
  intro x y h
  apply D.unitaryMap_injective f
  apply (MulAut.conj g⁻¹).injective
  exact congrArg Subtype.val h

def SubsystemData.intoModel {m : ℕ} (D : SubsystemData m F)
    (f : Three.QuadraticField m →+* F) (b : CoefficientField m →+* F)
    (g : AlgebraicPoints F)
    (hg : g * ((algebraicReeTwist m).onPoints g)⁻¹ = D.weyl) :
    (Three.form m).specialSubgroup →* Model m :=
  (fixedModelEquiv b).toMonoidHom.comp (D.intoFixed f g hg)

theorem SubsystemData.intoModel_injective {m : ℕ} (D : SubsystemData m F)
    (f : Three.QuadraticField m →+* F) (b : CoefficientField m →+* F)
    (g : AlgebraicPoints F)
    (hg : g * ((algebraicReeTwist m).onPoints g)⁻¹ = D.weyl) :
    Function.Injective (D.intoModel f b g hg) :=
  (fixedModelEquiv b).injective.comp (D.intoFixed_injective f g hg)

/-- The descent uses the actual coefficient-extension map on the literal matrix model. -/
theorem SubsystemData.intoModel_coefficient_image {m : ℕ} (D : SubsystemData m F)
    (f : Three.QuadraticField m →+* F) (b : CoefficientField m →+* F)
    (g : AlgebraicPoints F)
    (hg : g * ((algebraicReeTwist m).onPoints g)⁻¹ = D.weyl)
    (x : (Three.form m).specialSubgroup) :
    ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.modelEmbedding b
      (D.intoModel f b g hg x) = g⁻¹ * D.unitaryMap f x * g := by
  have he := congrArg Subtype.val
    ((fixedModelEquiv b).symm_apply_apply (D.intoFixed f g hg x))
  rw [fixedModelEquiv_symm_val] at he
  simpa only [intoModel, intoFixed, MonoidHom.comp_apply, MonoidHom.codRestrict_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using he

/-- Full SU₃ embeds in the literal Ree model once the split subsystem is constructed.
Lang conjugacy, rational descent, and scalar-center faithfulness are discharged. -/
theorem SubsystemData.exists_embedding {m : ℕ} (D : SubsystemData m F) (hm : 1 ≤ m)
    (f : Three.QuadraticField m →+* F) (b : CoefficientField m →+* F) :
    ∃ j : (Three.form m).specialSubgroup →* Model m, Function.Injective j := by
  obtain ⟨g, hg⟩ := algebraicReeTwist_lang (F := F) m hm D.weyl
  exact ⟨D.intoModel f b g hg, D.intoModel_injective f b g hg⟩

/-- The required product-torus consumer, preserving both full norm-one factors. -/
theorem SubsystemData.nonempty_product {m : ℕ} (D : SubsystemData m F) (hm : 1 ≤ m)
    (f : Three.QuadraticField m →+* F) (b : CoefficientField m →+* F) :
    Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1)) := by
  obtain ⟨j, hj⟩ := D.exists_embedding hm f b
  exact ⟨productTorusEmbeddingOfSpecial j hj⟩


def quadraticEmbedding (m : ℕ) : Three.QuadraticField m →+* AlgebraicClosure (CoefficientField m) :=
  (IsAlgClosed.lift (R := ZMod 2) (S := Three.QuadraticField m)
    (M := AlgebraicClosure (CoefficientField m))).toRingHom

/-- Only the split A₂×A₂ realization remains; both field embeddings are supplied. -/
theorem exists_embedding_of_subsystem (m : ℕ) (hm : 1 ≤ m)
    (D : SubsystemData m (AlgebraicClosure (CoefficientField m))) :
    ∃ j : (Three.form m).specialSubgroup →* Model m, Function.Injective j :=
  D.exists_embedding hm (quadraticEmbedding m) (algebraMap _ _)

/-- Concrete product-torus application of the full unitary descent. -/
theorem nonempty_product_of_subsystem (m : ℕ) (hm : 1 ≤ m)
    (D : SubsystemData m (AlgebraicClosure (CoefficientField m))) :
    Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1)) := by
  obtain ⟨j, hj⟩ := exists_embedding_of_subsystem m hm D
  exact ⟨productTorusEmbeddingOfSpecial j hj⟩


end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent

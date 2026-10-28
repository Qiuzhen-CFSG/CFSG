module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagData
public import Theory.AlgebraicGroup.Representations.Exterior
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Plücker coordinates of full flags

The Plücker line of a `d`-dimensional subspace is the range of the `d`th
exterior power of its inclusion. It has dimension one. Exterior multiplication
by a vector annihilates the whole line exactly when that vector lies in the
original subspace; thus the line determines the subspace. This uses the actual
alternating exterior algebra, including in characteristic two.

The construction commutes with linear automorphisms. Taking the finite tuple
of these lines gives an injective equivariant map from the natural-indexed
`FullFlag`; all omitted tail terms equal the whole vector space. This is the
linear-algebraic part of the flag construction in Borel, *Linear Algebraic
Groups*, §11.1. Closedness of its image is a separate geometric assertion.
-/

@[expose] public noncomputable section

open scoped ExteriorAlgebra LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

universe u v
variable {k : Type u} [Field k] {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The exterior line of a subspace of dimension `d`. -/
def pluckerLine (d : ℕ) (W : Submodule k V) : Submodule k (⋀[k]^d V) :=
  LinearMap.range (exteriorPower.map d W.subtype)

theorem finrank_pluckerLine (d : ℕ) (W : Submodule k V)
    (hW : Module.finrank k W = d) : Module.finrank k (pluckerLine d W) = 1 := by
  rw [pluckerLine, LinearMap.finrank_range_of_inj
    (exteriorPower.map_injective_field W.subtype_injective), exteriorPower.finrank_eq,
    hW, Nat.choose_self]

/-- The Plücker point is defined by the actual exterior power of the inclusion. -/
def subspacePlucker (d : ℕ) (W : Submodule k V) (hW : Module.finrank k W = d) :
    ℙ k (⋀[k]^d V) :=
  Projectivization.mk'' (pluckerLine d W) (finrank_pluckerLine d W hW)

@[simp] theorem subspacePlucker_submodule (d : ℕ) (W : Submodule k V)
    (hW : Module.finrank k W = d) : (subspacePlucker d W hW).submodule = pluckerLine d W :=
  Projectivization.submodule_mk'' _ _

private theorem pluckerLine_eq_span (d : ℕ) (W : Submodule k V)
    (b : Module.Basis (Fin d) k W) :
    pluckerLine d W = k ∙ exteriorPower.map d W.subtype (exteriorPower.ιMulti k d b) := by
  have hn : exteriorPower.map d W.subtype (exteriorPower.ιMulti k d b) ≠ 0 :=
    (map_ne_zero_iff _ (exteriorPower.map_injective_field W.subtype_injective)).mpr
      (exteriorPower_ιMulti_finBasis_ne_zero d b)
  have hd : Module.finrank k W = d := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ⟨_, rfl⟩)
  · rw [finrank_span_singleton hn, finrank_pluckerLine d W hd]

/-- The Plücker line recovers its subspace by exterior multiplication by vectors.
This uses alternation, so the statement also holds in characteristic two. -/
theorem mem_iff_wedge_pluckerLine (d : ℕ) (W : Submodule k V)
    (hW : Module.finrank k W = d) (x : V) :
    x ∈ W ↔ ∀ z ∈ pluckerLine d W,
      ExteriorAlgebra.ι k x * (z : ExteriorAlgebra k V) = 0 := by
  let b : Module.Basis (Fin d) k W := (Module.finBasis k W).reindex (finCongr hW)
  let D : FiniteSubspaceTopWedgeData k W := ⟨d, b⟩
  have hx := D.range_iff_ι_mul_vector_eq_zero W.subtype W.subtype_injective x
  rw [Submodule.range_subtype] at hx
  rw [pluckerLine_eq_span d W b]
  constructor
  · intro hxW z hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change ExteriorAlgebra.ι k x * (c •
      ((exteriorPower.map d W.subtype D.vector : ⋀[k]^d V) : ExteriorAlgebra k V)) = 0
    rw [Algebra.mul_smul_comm, hx.mpr hxW, smul_zero]
  · intro h
    exact hx.mp (h _ (Submodule.mem_span_singleton_self _))

theorem subspacePlucker_injective (d : ℕ) :
    Function.Injective (fun W : {W : Submodule k V // Module.finrank k W = d} =>
      subspacePlucker d W.1 W.2) := by
  intro W U h
  apply Subtype.ext
  have hline := congrArg Projectivization.submodule h
  simp only [subspacePlucker_submodule] at hline
  ext x
  rw [mem_iff_wedge_pluckerLine d W.1 W.2, mem_iff_wedge_pluckerLine d U.1 U.2,
    hline]

omit [FiniteDimensional k V] in
private theorem projectivization_map_submodule {E : Type*} [AddCommGroup E] [Module k E]
    (f : V →ₗ[k] E) (hf : Function.Injective f) (p : ℙ k V) :
    (Projectivization.map f hf p).submodule = p.submodule.map f := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [Projectivization.map_mk, Projectivization.submodule_mk,
      Projectivization.submodule_mk, Submodule.map_span]
    simp

omit [FiniteDimensional k V] in
/-- Taking exterior lines commutes with a linear change of coordinates. -/
theorem pluckerLine_map (d : ℕ) (W : Submodule k V) (e : V ≃ₗ[k] V) :
    pluckerLine d (W.map e.toLinearMap) =
      (pluckerLine d W).map (exteriorPower.map d e.toLinearMap) := by
  let eW := e.submoduleMap W
  have hcomp : (W.map e.toLinearMap).subtype.comp eW.toLinearMap =
      e.toLinearMap.comp W.subtype := by
    ext x
    rfl
  have hs : LinearMap.range (exteriorPower.map d eW.toLinearMap) = ⊤ :=
    LinearMap.range_eq_top.mpr (exteriorPower.map_surjective eW.surjective)
  calc
    pluckerLine d (W.map e.toLinearMap) =
        LinearMap.range ((exteriorPower.map d (W.map e.toLinearMap).subtype).comp
          (exteriorPower.map d eW.toLinearMap)) :=
      (LinearMap.range_comp_of_range_eq_top _ hs).symm
    _ = LinearMap.range (exteriorPower.map d (e.toLinearMap.comp W.subtype)) := by
      rw [← exteriorPower.map_comp, hcomp]
    _ = (pluckerLine d W).map (exteriorPower.map d e.toLinearMap) := by
      rw [exteriorPower.map_comp, LinearMap.range_comp]
      rfl

theorem subspacePlucker_map (d : ℕ) (W : Submodule k V)
    (hW : Module.finrank k W = d) (e : V ≃ₗ[k] V) :
    subspacePlucker d (W.map e.toLinearMap) ((e.finrank_map_eq W).trans hW) =
      Projectivization.map (exteriorPower.map d e.toLinearMap)
        (exteriorPower.map_injective_field e.injective) (subspacePlucker d W hW) := by
  apply Projectivization.submodule_injective
  rw [subspacePlucker_submodule, projectivization_map_submodule,
    subspacePlucker_submodule, pluckerLine_map]

/-- The proper terms, including the harmless degree-zero exterior line, of a
full flag as Plücker coordinates. For dimension zero this is an empty tuple. -/
def flagPlucker (F : FullFlag k V) :
    (i : Fin (Module.finrank k V)) → ℙ k (⋀[k]^(i : ℕ) V) :=
  fun i => subspacePlucker i (F.subspace i)
    ((F.finrank_eq i).trans (min_eq_left (Nat.le_of_lt i.isLt)))

theorem fullFlag_subspace_eq_top (F : FullFlag k V) (i : ℕ)
    (hi : Module.finrank k V ≤ i) : F.subspace i = ⊤ :=
  Submodule.eq_top_of_finrank_eq ((F.finrank_eq i).trans (min_eq_right hi))

/-- A full flag is determined by its finite tuple of exterior lines. -/
theorem flagPlucker_injective : Function.Injective (flagPlucker (k := k) (V := V)) := by
  intro F F' h
  apply FullFlag.ext
  intro i
  by_cases hi : i < Module.finrank k V
  · have hcoord := congrFun h ⟨i, hi⟩
    have hF := (F.finrank_eq i).trans (min_eq_left (Nat.le_of_lt hi))
    have hF' := (F'.finrank_eq i).trans (min_eq_left (Nat.le_of_lt hi))
    have hs : (⟨F.subspace i, hF⟩ : {W : Submodule k V // Module.finrank k W = i}) =
        ⟨F'.subspace i, hF'⟩ := by
      apply subspacePlucker_injective i
      exact hcoord
    exact congrArg Subtype.val hs
  · rw [fullFlag_subspace_eq_top F i (Nat.le_of_not_gt hi),
      fullFlag_subspace_eq_top F' i (Nat.le_of_not_gt hi)]

/-- The coordinate action is the exterior power of the actual linear action. -/
theorem flagPlucker_map (F : FullFlag k V) (e : V ≃ₗ[k] V)
    (i : Fin (Module.finrank k V)) :
    flagPlucker (F.map e) i =
      Projectivization.map (exteriorPower.map i e.toLinearMap)
        (exteriorPower.map_injective_field e.injective) (flagPlucker F i) :=
  subspacePlucker_map i (F.subspace i)
    ((F.finrank_eq i).trans (min_eq_left (Nat.le_of_lt i.isLt))) e

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal.M23.Linear
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal.Orbit

/-!
# The seven source-orbit vectors in the M23 octad space

The intersection with the M23 weight-two orbit consists exactly of the seven
pairs through the fixed point. The inclusion in the nonsingular set is retained
as an inclusion; the full nonsingular set belongs to the M24 orbit calculation.

Source: Aschbacher--Smith, H.15.2, printed p.399.
-/

@[expose] public section
noncomputable section
open scoped Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.CocodeOctad

/-- A pair through the point fixed by M23 and a remaining octad coordinate. -/
def sevenPair (O : Octad) (i : octadSeven O) : PointPair :=
  ⟨{0, i.val}, by simp [Ne.symm (Finset.mem_erase.mp i.property).1]⟩

/-- The seven vectors singled out on printed p.399. -/
def sevenPairVector (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (i : octadSeven O) : supportedPairSpace O.val :=
  ⟨pairVector (sevenPair O i), pairVector_mem_supportedPairSpace _ (by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hO
    · exact Finset.mem_singleton.mp hx ▸ (Finset.mem_erase.mp i.property).2)⟩

lemma sevenPairVector_injective (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Function.Injective (sevenPairVector O hO) := by
  intro i j h
  have he := congrArg Subtype.val (pairVector_injective (congrArg Subtype.val h))
  have hm : i.val ∈ (sevenPair O i).val := by simp [sevenPair]
  rw [he] at hm
  apply Subtype.ext
  simpa [sevenPair, (Finset.mem_erase.mp i.property).1] using hm

lemma sevenPairVector_equivariant (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : m23OctadStabilizer O) (i : octadSeven O) :
    m23PairRepresentation O g (sevenPairVector O hO i) =
      sevenPairVector O hO (sevenCoordinateAction O hO g i) := by
  apply Subtype.ext
  change cocodeRepresentation (pointEmbedding g.val) (pairVector (sevenPair O i)) = _
  rw [pairVector_equivariant]
  apply congrArg pairVector
  apply Subtype.ext
  change pointEmbedding g.val • {0, i.val} = {0, (sevenCoordinateAction O hO g i).val}
  simp only [Finset.smul_finset_def, Finset.image_insert, Finset.image_singleton]
  have hz : pointEmbedding g.val • (0 : Fin 24) = 0 := pointEmbedding_fixed g.val
  rw [hz, sevenCoordinateAction_apply]
  rfl

lemma sevenPairVector_range (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Set.range (sevenPairVector O hO) =
      {v : supportedPairSpace O.val | v.val ∈ m23WeightTwoOrbit} := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    let j := m23PointEquiv.symm ⟨i.val, (Finset.mem_erase.mp i.property).1⟩
    have hj : m23PointEmbedding j = i.val :=
      congrArg Subtype.val (m23PointEquiv.apply_symm_apply _)
    refine ⟨j, ?_⟩
    change pairVector (pointPair j) = pairVector (sevenPair O i)
    apply congrArg pairVector
    apply Subtype.ext
    change {0, m23PointEmbedding j} = {0, i.val}
    rw [hj]
  · rintro ⟨j, hj⟩
    have hs : (pointPair j).val ⊆ O.val :=
      (pairVector_mem_supportedPairSpace_iff O (pointPair j)).mp (show m23PairVector j ∈ supportedPairSpace O.val from hj.symm ▸ v.property)
    let i : octadSeven O := ⟨m23PointEmbedding j, Finset.mem_erase.mpr
      ⟨embeddedPoint_ne_zero j, hs (by simp [pointPair])⟩⟩
    exact ⟨i, Subtype.ext hj⟩

lemma card_m23_sourceOrbit (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Nat.card {v : supportedPairSpace O.val | v.val ∈ m23WeightTwoOrbit} = 7 := by
  rw [← sevenPairVector_range O hO,
    ← Nat.card_congr (Equiv.ofInjective _ (sevenPairVector_injective O hO)),
    Nat.card_eq_fintype_card, Fintype.card_coe, octadSeven_card O hO]

lemma m23_sourceOrbit_nonsingular (O : Octad) (v : supportedPairSpace O.val)
    (hv : v.val ∈ m23WeightTwoOrbit) : quadratic O v = 1 :=
  (quadratic_one_iff_weightTwo O v).mpr (m23WeightTwoOrbit_subset hv)

end MathieuCode.CocodeOctad

module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadOvergroup
public import Theory.Representation.SL2FourNaturalOrbits.RelativeTraceForm

/-!
# Scalar choices of the original endpoint marking

Multiplication of the natural F₄ coordinates by a nonzero scalar commutes
with the whole endpoint quotient. It therefore gives new natural endpoint
data on the same original subgroup, with the same complement, quotient,
symplectic embedding and binary normalizer marking. The determinant of two
marked kernel vectors is multiplied by the square of that scalar.
-/

public noncomputable section
namespace CFSG.Quasithin.HigmanSims
open Representation.SL2FourNatural
open scoped Matrix
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]

/-- Nonzero scalar change of the actual endpoint field coordinates. -/
@[expose] def NaturalEndpointData.scalarRemarking (d : NaturalEndpointData A)
    (c : F) (hc : c ≠ 0) : NaturalEndpointData A :=
  { d with
    coordinates := d.coordinates.trans (scalarCoordinates c hc).toAddEquiv.toMultiplicative
    field_coordinates := (scalarCoordinates c hc).symm.trans d.field_coordinates
    action := by
      intro g a
      change Multiplicative.ofAdd (scalarCoordinates c hc
        (d.coordinates (A.normalizerMonoidHom (Subgroup.inclusion d.normalizes g) a)).toAdd) =
        Multiplicative.ofAdd (Representation.SL2FourNatural.action (d.quotient g)
          (scalarCoordinates c hc (d.coordinates a).toAdd))
      rw [d.action]
      exact congrArg Multiplicative.ofAdd (scalarCoordinates_action c hc _ _)
    embedding_action := by
      intro g w
      change (d.embedding g).val *ᵥ d.field_coordinates ((scalarCoordinates c hc).symm w) =
        d.field_coordinates ((scalarCoordinates c hc).symm (Representation.SL2FourNatural.action g w))
      rw [d.embedding_action]
      congr 1
      apply (scalarCoordinates c hc).injective
      rw [scalarCoordinates_action, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
    coordinate_marking := by
      intro a
      change scalarCoordinates c hc (d.coordinates a).toAdd =
        scalarCoordinates c hc (d.field_coordinates.symm (d.binary_coordinates (Additive.ofMul a)))
      rw [d.coordinate_marking] }

/-- The scalar remarking retains the actual ambient groups and all quotient
and binary coordinates, including the six-letter map and its even preimage. -/
theorem NaturalEndpointData.scalarRemarking_retains_source (d : NaturalEndpointData A)
    (c : F) (hc : c ≠ 0) :
    (d.scalarRemarking c hc).carrier = d.carrier ∧
    (d.scalarRemarking c hc).complement = d.complement ∧
    (d.scalarRemarking c hc).quotient = d.quotient ∧
    (d.scalarRemarking c hc).embedding = d.embedding ∧
    (d.scalarRemarking c hc).binary_coordinates = d.binary_coordinates ∧
    (d.scalarRemarking c hc).symplectic_quotient = d.symplectic_quotient ∧
    (d.scalarRemarking c hc).six_letter_quotient = d.six_letter_quotient ∧
    (d.scalarRemarking c hc).hexad_overgroup = d.hexad_overgroup := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The new kernel coordinates are literal scalar multiples of the old ones. -/
theorem NaturalEndpointData.scalarRemarking_coordinates (d : NaturalEndpointData A)
    (c : F) (hc : c ≠ 0) (a : A) :
    ((d.scalarRemarking c hc).coordinates a).toAdd = c • (d.coordinates a).toAdd := rfl

/-- Scalar remarking changes the determinant of two original kernel
elements by precisely the square of the chosen scalar. -/
theorem NaturalEndpointData.scalarRemarking_wedge (d : NaturalEndpointData A)
    (c : F) (hc : c ≠ 0) (a b : A) :
    wedge ((d.scalarRemarking c hc).coordinates a).toAdd
      ((d.scalarRemarking c hc).coordinates b).toAdd =
      c ^ 2 * wedge (d.coordinates a).toAdd (d.coordinates b).toAdd := by
  rw [d.scalarRemarking_coordinates, d.scalarRemarking_coordinates]
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

private theorem scalar_for_wedge (s t : F) (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ c ^ 2 * s = t := by
  revert s t
  decide +kernel

/-- For two independent original kernel vectors, every nonzero determinant
is attained by a source marking on the same endpoint and binary normalizer.
The new marking is obtained by an actual scalar, rather than an assumed
endpoint or ambient extension. -/
theorem NaturalEndpointData.exists_scalarRemarking_wedge (d : NaturalEndpointData A)
    (a b : A) (hab : wedge (d.coordinates a).toAdd (d.coordinates b).toAdd ≠ 0)
    (t : F) (ht : t ≠ 0) :
    ∃ (c : F) (hc : c ≠ 0),
      wedge ((d.scalarRemarking c hc).coordinates a).toAdd
        ((d.scalarRemarking c hc).coordinates b).toAdd = t := by
  obtain ⟨c, hc, he⟩ := scalar_for_wedge _ t hab ht
  exact ⟨c, hc, (d.scalarRemarking_wedge c hc a b).trans he⟩

private theorem source_form_nonzero (d : NaturalEndpointData A) :
    (Theory.SpecificGroups.SymplecticFour.form (ZMod 2)).comp
      d.field_coordinates.toLinearMap d.field_coordinates.toLinearMap ≠ 0 := by
  intro he
  let x : Theory.SpecificGroups.SymplecticFour.Vector (ZMod 2) := Pi.single (.inl 0) 1
  let y : Theory.SpecificGroups.SymplecticFour.Vector (ZMod 2) := Pi.single (.inr 0) 1
  have hh := congrArg (fun B => B (d.field_coordinates.symm x) (d.field_coordinates.symm y)) he
  change Theory.SpecificGroups.SymplecticFour.form (ZMod 2)
    (d.field_coordinates (d.field_coordinates.symm x))
    (d.field_coordinates (d.field_coordinates.symm y)) = 0 at hh
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hh
  have hxy : Theory.SpecificGroups.SymplecticFour.form (ZMod 2) x y = 1 := by
    decide +kernel
  rw [hxy] at hh
  exact one_ne_zero hh

/-- The original endpoint admits every nonzero relative trace-form
coefficient through a scalar remarking. Its physical actors and the whole
binary normalizer marking stay fixed. -/
theorem NaturalEndpointData.exists_scalarRemarking_relative_form (d : NaturalEndpointData A)
    (t : F) (ht : t ≠ 0) :
    ∃ (c : F) (hc : c ≠ 0), ∀ v w : V,
      Theory.SpecificGroups.SymplecticFour.form (ZMod 2)
        ((d.scalarRemarking c hc).field_coordinates v)
        ((d.scalarRemarking c hc).field_coordinates w) =
          QuadraticAlgebra.trace (t * wedge v w) := by
  let B := (Theory.SpecificGroups.SymplecticFour.form (ZMod 2)).comp
    d.field_coordinates.toLinearMap d.field_coordinates.toLinearMap
  have hB (g : SL) (v w : V) : B (Representation.SL2FourNatural.action g v) (Representation.SL2FourNatural.action g w) = B v w := by
    change Theory.SpecificGroups.SymplecticFour.form (ZMod 2)
      (d.field_coordinates (Representation.SL2FourNatural.action g v)) (d.field_coordinates (Representation.SL2FourNatural.action g w)) = _
    rw [←d.embedding_action, ←d.embedding_action]
    exact Theory.SpecificGroups.SymplecticFour.preserves_form (d.embedding g) _ _
  obtain ⟨s, hs⟩ := invariant_binary_form_eq_trace B hB
  have hs0 : s ≠ 0 := by
    intro he
    apply source_form_nonzero d
    change B = 0
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change B v w = 0
    rw [hs, he, zero_mul]
    exact map_zero QuadraticAlgebra.trace
  obtain ⟨c, hc, he⟩ := scalar_for_wedge t s ht hs0
  refine ⟨c, hc, fun v w => ?_⟩
  change B ((scalarCoordinates c hc).symm v) ((scalarCoordinates c hc).symm w) = _
  obtain ⟨v, rfl⟩ := (scalarCoordinates c hc).surjective v
  obtain ⟨w, rfl⟩ := (scalarCoordinates c hc).surjective w
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hs]
  congr 1
  rw [scalarCoordinates_apply, scalarCoordinates_apply]
  calc
    s * wedge v w = (c ^ 2 * t) * wedge v w := by rw [he]
    _ = t * wedge (c • v) (c • w) := by
      simp only [wedge, Pi.smul_apply, smul_eq_mul]
      ring

end CFSG.Quasithin.HigmanSims

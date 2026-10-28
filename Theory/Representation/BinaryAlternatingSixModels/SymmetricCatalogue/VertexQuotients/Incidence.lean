module

public import Theory.Representation.BinaryDuadStructure.LineQuotient
public import Theory.Representation.BinaryDuadStructure.OppositeCover.Geometry
public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.Building

/-!
# Incidence squares on the two S₆ vertex modules

The incidence matrix and its transpose are equivariant for the literal point
and line actions. Their squares send basis vectors to the constant vector plus
a natural complement. On the line side the complement is identified through
the already marked pentad correspondence, which intertwines with `diagramAut`.
The identities are checked on the fifteen geometric basis vectors.

These maps supply the two possible factorizations in `VertexQuotients`.
In particular, no involutivity assumption on the marked automorphism is needed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.1–3,
printed pp.342–345, using the perpendicular-complement geometry of G.5.3(4–5).
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule
open BinaryDuadStructure BinaryDuadStructure.OppositeCover Representation
namespace BinaryAlternatingSix.SymmetricCatalogue.VertexQuotients

def pencil (d : Duad) : Full Syntheme := fun s => if incident d s then 1 else 0

def incidenceLinear : Full Syntheme →ₗ[ZMod 2] Full Duad :=
  Fintype.linearCombination (ZMod 2) line

def transposeLinear : Full Duad →ₗ[ZMod 2] Full Syntheme :=
  Fintype.linearCombination (ZMod 2) pencil

@[simp] theorem incidence_single (s : Syntheme) :
    incidenceLinear (Pi.single s 1) = line s := by
  simp [incidenceLinear, Fintype.linearCombination_apply_single]

@[simp] theorem transpose_single (d : Duad) :
    transposeLinear (Pi.single d 1) = pencil d := by
  simp [transposeLinear, Fintype.linearCombination_apply_single]

private theorem pointAction_line (g : S6) (s : Syntheme) :
    pointAction g (line s) = line (synthemeAct g s) := by
  ext d
  have he := incident_act_iff g (g⁻¹ • d) s
  rw [smul_inv_smul] at he
  change (if incident (g⁻¹ • d) s then (1 : ZMod 2) else 0) =
    if incident d (synthemeAct g s) then 1 else 0
  simp only [he]

private theorem lineAction_pencil (g : S6) (d : Duad) :
    lineRepresentation g (pencil d) = pencil (g • d) := by
  ext s
  have he := incident_act_iff g d (synthemeAct g⁻¹ s)
  rw [← synthemeAct_mul, mul_inv_cancel, synthemeAct_one] at he
  change (if incident d (synthemeAct g⁻¹ s) then (1 : ZMod 2) else 0) =
    if incident (g • d) s then 1 else 0
  simp only [he]

noncomputable def incidence : lineRepresentation.IntertwiningMap pointAction :=
  incidenceLinear.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g u
    change (∑ s, u (synthemeAct g⁻¹ s) • line s) = pointAction g (∑ s, u s • line s)
    rw [map_sum]
    simp only [map_smul, pointAction_line]
    exact (Equiv.sum_comp (linePerm g)
      (fun s => u (synthemeAct g⁻¹ s) • line s)).symm.trans (by
        change (∑ s, u (synthemeAct g⁻¹ (synthemeAct g s)) • line (synthemeAct g s)) = _
        simp only [← synthemeAct_mul, inv_mul_cancel, synthemeAct_one]))

noncomputable def incidenceTranspose : pointAction.IntertwiningMap lineRepresentation :=
  transposeLinear.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g u
    change (∑ d, u (g⁻¹ • d) • pencil d) = lineRepresentation g (∑ d, u d • pencil d)
    rw [map_sum]
    simp only [map_smul, lineAction_pencil]
    exact (Equiv.sum_comp (MulAction.toPerm g)
      (fun d => u (g⁻¹ • d) • pencil d)).symm.trans (by
        simp only [MulAction.toPerm_apply, inv_smul_smul]))

def lineRelabel : Full Duad ≃ₗ[ZMod 2] Full Syntheme :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) linePoint

@[simp] theorem lineRelabel_apply (u : Full Duad) (s : Syntheme) :
    lineRelabel u s = u (linePoint s) := rfl

noncomputable def lineRelabelEquiv :
    Representation.Equiv (pointAction.comp diagramAut.toMonoidHom) lineRepresentation :=
  Representation.Equiv.mk lineRelabel (by
    intro g
    apply LinearMap.ext
    intro u
    ext s
    change u ((diagramAut g)⁻¹ • linePoint s) = u (linePoint (synthemeAct g⁻¹ s))
    rw [linePoint_equivariant, map_inv])

theorem lineRelabel_line (s : Syntheme) : lineRelabel (line s) = pencil (dualLine s) := by
  ext t
  change (if incident (linePoint t) s then (1 : ZMod 2) else 0) =
    if incident (dualLine s) t then 1 else 0
  have h : incident (linePoint t) s ↔ incident (dualLine s) t := by
    simpa only [linePoint.symm_apply_apply] using dual_incidence s (linePoint t)
  simp only [h]

noncomputable def pointNaturalEmbedding : firstNatural.IntertwiningMap pointAction :=
  complementMap.intertwiningMap_of_isIntertwiningMap _ _ complementMap_equivariant

noncomputable def lineNaturalEmbedding : secondNatural.IntertwiningMap lineRepresentation := {
  toLinearMap := lineRelabel.toLinearMap.comp complementMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change lineRelabel (complementMap (firstNatural (diagramAut g) v)) =
      lineRepresentation g (lineRelabel (complementMap v))
    rw [complementMap_equivariant]
    exact IntertwiningMap.isIntertwining (pointAction.comp diagramAut.toMonoidHom)
      lineRepresentation lineRelabelEquiv.toIntertwiningMap g (complementMap v) }

/-- The point-side incidence square is the orthogonality matrix. -/
theorem incidence_square_single (d : Duad) :
    incidenceLinear (transposeLinear (Pi.single d 1)) =
      allOne Duad + complementMap (polarVector d).val := by
  rw [transpose_single]
  fin_cases d <;> decide

/-- Pentad duality identifies the other incidence square with the marked opposite polar form. -/
theorem transpose_square_single (s : Syntheme) :
    transposeLinear (incidenceLinear (Pi.single s 1)) =
      allOne Syntheme + lineRelabel (complementMap (polarVector (linePoint s)).val) := by
  rw [incidence_single]
  fin_cases s <;> decide

end BinaryAlternatingSix.SymmetricCatalogue.VertexQuotients

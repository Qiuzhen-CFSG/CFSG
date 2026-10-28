module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Sextet.Layers
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.Calculation

/-!
# The sextet–trio crossing used in 8.2.12

Compatible partitions put the sextet seven-space inside the trio nine-space,
which is the commutator with the actual perfect residual. Their proved
dimensions exclude containment in the trio's fixed three-space. Thus the
native cocode supplies the source vector in V_z ∩ B outside U.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.15.8 as
used in 8.2.12, printed pp.402 and 722. Transport to the source subgroups
still uses their marked module identifications.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open Representation.BinaryOffender
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups

namespace CFSG.Quasithin.Chapter8.Section02.Centralizer

/-- H.15.8's comparison in compatible native coordinates. The actor on the
right is the actual perfect residual, not the two-core or whole stabilizer. -/
theorem sextet_trio_crossing (S : Sextet) (T : Trio)
    (hrefines : ∀ B ∈ S.parts, ∃ O ∈ T.parts, B ⊆ O) :
    sextetPairSpace S ≤ subspaceCommutator cocodeRepresentation ⊤ (trioResidual T) ∧
      ¬ sextetPairSpace S ≤ trioFixedSpace T := by
  constructor
  · rw [← trioPairSpace_eq_residual_commutator]
    exact sextetPairSpace_le_trioPairSpace S T hrefines
  · intro h
    have hd := Submodule.finrank_mono h
    rw [sextetPairSpace_finrank, finrank_trioFixedSpace] at hd
    omega

/-- In the source's compatible standard sextet and trio, there is a vector
of V_z inside B=[V,L_U] but outside U=C_V(K_T). -/
theorem exists_sextet_vector_in_residual_commutator_not_fixed :
    ∃ v : Cocode, v ∈ sextetPairSpace standardSextet ∧
      v ∈ subspaceCommutator cocodeRepresentation ⊤ (trioResidual standardTrio) ∧
      v ∉ trioFixedSpace standardTrio := by
  obtain ⟨hle, hnot⟩ := sextet_trio_crossing standardSextet standardTrio
    standardSextet_refines_standardTrio
  obtain ⟨v, hv, hnv⟩ := SetLike.not_le_iff_exists.mp hnot
  exact ⟨v, hv, hle hv, hnv⟩

end CFSG.Quasithin.Chapter8.Section02.Centralizer

module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.IncidenceTransport
/-!
# Cardinality of the native sextets

The literal point-permutation action and the existing sextet transporter
identify the stabilizer of the standard sextet. Its proved order gives
1771 sextets, independently of the plane-hitting certificate.

Source: AS91 §3; the native sextet stabilizer order is in `SextetCore`.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.Stabilizers
open scoped Pointwise
noncomputable instance : MulAction M24 Plane where
  smul := conjugateSextet
  one_smul π := by apply plane_parts_injective; exact one_smul M24 π.parts
  mul_smul g k π := by apply plane_parts_injective; exact mul_smul g k π.parts
noncomputable instance : Finite Plane := Finite.of_injective Sextet.parts plane_parts_injective
instance : MulAction.IsPretransitive M24 Plane where
  exists_smul_eq := by
    intro π σ
    obtain ⟨g,hg⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator π
    obtain ⟨k,hk⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator σ
    refine ⟨k * g⁻¹,plane_parts_injective ?_⟩
    change (k * g⁻¹) • π.parts = σ.parts
    rw [←hg,mul_smul,inv_smul_smul,hk]
theorem plane_card : Nat.card Plane = 1771 := by
  have he : MulAction.stabilizer M24 standardSextet = sextetStabilizer standardSextet := by
    ext g
    exact ⟨fun h => congrArg Sextet.parts h,fun h => plane_parts_injective h⟩
  have hi := MulAction.index_stabilizer_of_transitive M24 standardSextet
  have hc := Subgroup.card_mul_index (MulAction.stabilizer M24 standardSextet)
  rw [he,SextetCore.stabilizer_card,m24_order] at hc
  rw [he] at hi
  rw [hi] at hc
  change 138240 * Nat.card Plane = 244823040 at hc
  omega
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native

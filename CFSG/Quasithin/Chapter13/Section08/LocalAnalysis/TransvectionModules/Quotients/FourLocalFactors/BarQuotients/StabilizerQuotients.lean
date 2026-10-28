module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.ChiefCubicCores
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.PlaneGeometry

/-!
# The two natural stabilizer quotients

The syntheme two-core is the proved cube D. A Sylow subgroup has index
three and properly contains D, so its three-coset action identifies the
intrinsic two-core quotient with S₃. The line quotient is transported from
the actual duad stabilizer. Sylow conjugacy and uniqueness of the canonical
binary flag then give both quotients for any Sylow-stable source line or
plane, retaining the conjugating permutation.

Source: Aschbacher–Smith, Notation 13.2.1 and the natural flag of §B.3;
the group quotients used in 13.8.6(4), printed p.948.
-/

@[expose] public section

open Subgroup
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.BarQuotients
open TransvectionParabolic.EarlierCore

theorem syntheme_quotient : Nonempty ((H2 ⧸ pCore 2 H2) ≃* Equiv.Perm (Fin 3)) := by
  let B := borel.subgroupOf H2
  have hp : IsPGroup 2 B := borelSylow.isPGroup'.comap_subtype
  have hi : B.index = 3 := borel_relIndex_syntheme
  let Q : Sylow 2 H2 := hp.toSylow (by rw [hi]; decide)
  apply sylow_index_three_core_quotient Q hi
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal Q)
  intro he
  have hm := congrArg (fun J : Subgroup H2 => J.map H2.subtype) he
  change H2.pCoreIn 2 = B.map H2.subtype at hm
  rw [H2_core_eq_D] at hm
  have hb : B.map H2.subtype = borel :=
    map_subgroupOf_eq_of_le (show borel ≤ H2 from borel_le_synthemeStabilizer)
  rw [hb] at hm
  have hc := congrArg (fun J : Subgroup (Equiv.Perm (Fin 6)) => Nat.card J) hm
  rw [D_card, borel_order] at hc
  contradiction

private def swapDuad : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 1 5

private theorem H1_map_duad : H1.map (MulAut.conj swapDuad).toMonoidHom = duadStabilizer := by
  change (MulAction.stabilizer (Equiv.Perm (Fin 6)) (pair 4 5)).map _ = _
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have h : swapDuad • pair 4 5 = pair 0 1 := by decide
  rw [h]
  rfl

theorem point_quotient : Nonempty ((H1 ⧸ pCore 2 H1) ≃* Equiv.Perm (Fin 3)) := by
  let e : H1 ≃* duadStabilizer := ((MulAut.conj swapDuad).subgroupMap H1).trans
    (MulEquiv.subgroupCongr H1_map_duad)
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans duadCoreQuotientEquiv⟩


local notation "r" => BinaryPermutation.naturalRepresentation (Fin 6)
private theorem conjugate_stabilizes (W : Submodule (ZMod 2) (natural (Fin 6)))
    (g h : Equiv.Perm (Fin 6)) (hh : h ∈ subspaceStabilizer r W) :
    g * h * g⁻¹ ∈ subspaceStabilizer r (W.map (r g)) := by
  apply (mem_stabilizer_iff_map _ _).mpr
  have hh' := (mem_stabilizer_iff_map _ _).mp hh
  simp only [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  rw [← Submodule.map_comp (r g) (r g⁻¹),
    ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_eq_id, Submodule.map_id, hh']

theorem map_stabilizer (W : Submodule (ZMod 2) (natural (Fin 6)))
    (g : Equiv.Perm (Fin 6)) :
    (subspaceStabilizer r W).map (MulAut.conj g).toMonoidHom =
      subspaceStabilizer r (W.map (r g)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact conjugate_stabilizes W g x hx
  · intro x hx
    have hb : (W.map (r g)).map (r g⁻¹) = W := by
      rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_eq_id, Submodule.map_id]
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have hh := conjugate_stabilizes (W.map (r g)) g⁻¹ x hx
      rw [inv_inv, hb] at hh
      exact hh
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem stabilizer_quotient (S : Subgroup (Equiv.Perm (Fin 6)))
    (hS : alternatingGroup (Fin 6) ≤ S) (Q : Sylow 2 S)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hd : Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 2)
    (hi : (Q : Subgroup S).map S.subtype ≤ subspaceStabilizer r W) :
    Nonempty ((subspaceStabilizer r W ⧸ pCore 2 (subspaceStabilizer r W)) ≃*
      Equiv.Perm (Fin 3)) := by
  obtain ⟨g, hg⟩ := PlaneGeometry.exists_conjugate_T0_le S hS Q
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv ((BinaryPermutation.naturalRepresentation (Fin 6)).asGroupHom g.val⁻¹)
  have hstable := PlaneGeometry.aligned_invariant S Q g hg W hi
  have hdim := e.finrank_map_eq W
  rcases hd with hd | hd
  · have hcan : W.map (r g.val⁻¹) = canonicalLine :=
      canonicalLine_unique _ (hdim.trans hd) hstable
    have hmap : (subspaceStabilizer r W).map (MulAut.conj g.val⁻¹).toMonoidHom = H1 := by
      rw [map_stabilizer, hcan]
      ext x
      exact (mem_stabilizer_iff_map _ _).trans (canonicalLine_stabilizer x)
    let c : subspaceStabilizer r W ≃* H1 :=
      ((MulAut.conj g.val⁻¹).subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
    exact ⟨(QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans point_quotient.some⟩
  · have hcan : W.map (r g.val⁻¹) = canonicalPlane :=
      canonicalPlane_unique _ (hdim.trans hd) hstable
    have hmap : (subspaceStabilizer r W).map (MulAut.conj g.val⁻¹).toMonoidHom = H2 := by
      rw [map_stabilizer, hcan]
      ext x
      exact (mem_stabilizer_iff_map _ _).trans (canonicalPlane_stabilizer x)
    let c : subspaceStabilizer r W ≃* H2 :=
      ((MulAut.conj g.val⁻¹).subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
    exact ⟨(QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans syntheme_quotient.some⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.BarQuotients

end

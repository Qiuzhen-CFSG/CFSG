module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.PlaneGeometry

/-!
# The plane generates the hyperplane under the point residual

Align the actual Sylow flag with the duad–syntheme flag. The cubic (012)
fixes the duad {4,5}, belongs to the point residual, and moves the canonical
plane. Its orbit therefore has dimension at least three. Invariance of
the perpendicular bounds that dimension by three and identifies the span.

Source: Aschbacher–Smith, §B.3, pp.83–85; source flag generation used in
13.8.6 on p.948 and the compatible cover marking.
-/

public section
open Subgroup Module BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.PlaneGeometry
local notation "r" => naturalRepresentation (Fin 6)

/-- The literal binary point residual generates its perpendicular from the
Sylow-stable plane. The actor is the residual, not the larger duad intersection. -/
theorem flag_generation (S : Subgroup (Equiv.Perm (Fin 6)))
    (hS : alternatingGroup (Fin 6) ≤ S) (Q : Sylow 2 S)
    (P D : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1)
    (hD : Module.finrank (ZMod 2) D = 2)
    (hPi : (Q : Subgroup S).map S.subtype ≤ subspaceStabilizer r P)
    (hDi : (Q : Subgroup S).map S.subtype ≤ subspaceStabilizer r D)
    (hDP : D ≤ form.orthogonal P) :
    Submodule.span (ZMod 2) {v : V |
      ∃ a ∈ residual (S ⊓ subspaceStabilizer r P), ∃ w ∈ D, r a w = v} =
        form.orthogonal P := by
  let A := residual (S ⊓ subspaceStabilizer r P)
  let W := Submodule.span (ZMod 2) {v : V | ∃ a ∈ A, ∃ w ∈ D, r a w = v}
  have hDW : D ≤ W := by
    intro w hw
    exact Submodule.subset_span ⟨1, A.one_mem, w, hw, by simp⟩
  have hWP : W ≤ form.orthogonal P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, w, hw, rfl⟩
    have hp := (stabilizer_le_orthogonal_stabilizer P) ((residual_le _ ha).2)
    exact (hp w).mpr (hDP hw)
  obtain ⟨g, hg⟩ := exists_conjugate_T0_le S hS Q
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv ((naturalRepresentation (Fin 6)).asGroupHom g.val⁻¹)
  have hPc : P.map (r g.val⁻¹) = canonicalLine :=
    canonicalLine_unique _ ((e.finrank_map_eq P).trans hP)
      (aligned_invariant S Q g hg P hPi)
  have hDc : D.map (r g.val⁻¹) = canonicalPlane :=
    canonicalPlane_unique _ ((e.finrank_map_eq D).trans hD)
      (aligned_invariant S Q g hg D hDi)
  have hback (B E : Submodule (ZMod 2) V) (he : B.map (r g.val⁻¹) = E) :
      E.map (r g.val) = B := by
    rw [← he, ← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_eq_id, Submodule.map_id]
  let c := g.val * cycle012 * g.val⁻¹
  have hcP : c ∈ subspaceStabilizer r P := by
    apply (mem_stabilizer_iff_map _ _).mpr
    rw [← hback P _ hPc]
    change (canonicalLine.map (r g.val)).map (r (g.val * cycle012 * g.val⁻¹)) = _
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul]
    have hm : (g.val * cycle012 * g.val⁻¹) * g.val = g.val * cycle012 := by group
    rw [hm, map_mul, Module.End.mul_eq_comp, Submodule.map_comp,
      canonicalLine_map_of_mem (by decide : cycle012 ∈ H1)]
  have hcS : c ∈ S := S.mul_mem (S.mul_mem g.property
    (hS (by change Equiv.Perm.sign cycle012 = 1; decide))) (S.inv_mem g.property)
  let C := S ⊓ subspaceStabilizer r P
  let cC : C := ⟨c, hcS, hcP⟩
  have hc3 : cC ^ 3 = 1 := by
    apply Subtype.ext
    change (g.val * cycle012 * g.val⁻¹) ^ 3 = 1
    rw [← MulAut.conj_apply, ← map_pow, show cycle012 ^ 3 = 1 from by decide, map_one]
  have hc : c ∈ A := ⟨cC, mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hc3)), rfl⟩
  have hwD : r g.val (pairVector 0 1) ∈ D := by
    rw [← hback D _ hDc]
    exact Submodule.mem_map_of_mem (Submodule.subset_span (by simp))
  have hmove : r c (r g.val (pairVector 0 1)) = r g.val (pairVector 1 2) := by
    rw [← Module.End.mul_apply, ← map_mul]
    have he : c * g.val = g.val * cycle012 := by dsimp [c]; group
    rw [he, map_mul, Module.End.mul_apply, pairVector_map]
    rfl
  have hwW : r g.val (pairVector 1 2) ∈ W :=
    Submodule.subset_span ⟨c, hc, r g.val (pairVector 0 1), hwD, hmove⟩
  have hwN : r g.val (pairVector 1 2) ∉ D := by
    intro h
    have hh := Submodule.mem_map_of_mem (f := r g.val⁻¹) h
    rw [hDc, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at hh
    exact (by
      rw [pairVector_mem_plane_iff (by decide : (1 : Fin 6) ≠ 2)]
      decide : pairVector 1 2 ∉ canonicalPlane) hh
  have hlt : D < W := lt_of_le_of_ne hDW (by intro h; exact hwN (h.symm ▸ hwW))
  have hdW := Submodule.finrank_lt_finrank_of_lt hlt
  have hdW' := Submodule.finrank_mono hWP
  have hperp : Module.finrank (ZMod 2) (form.orthogonal P) = 3 := by
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      finrank_natural_even (Fin 6) (by decide), hP]
    rfl
  rw [hD] at hdW
  rw [hperp] at hdW'
  change W = form.orthogonal P
  apply Submodule.eq_of_le_of_finrank_eq hWP
  rw [hperp]
  omega

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.PlaneGeometry

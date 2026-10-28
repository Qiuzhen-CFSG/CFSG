module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.RankOneGeometry
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.BinaryComplement
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Marking
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Generation
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.SylowPlacement
public import Mathlib.LinearAlgebra.Projection

/-!
# Source B.4.9(1) splitting used by the reducible B.5.1 induction

The marked four-group and axis geometry produce a local complement to the
actual natural submodule. Its Sylow placement makes the axis-Levi product
of odd index. Averaging the local projection over its cosets makes the map
equivariant for the ambient actor. The kernel is therefore
an invariant complement to the original submodule. Both quotient orientations
are retained.

This closes the exact B.4.9(1) premise consumed by the existing B.4.9(2)
FF consequences. It introduces no classification or target-bearing premise.
Source: Aschbacher--Smith, B.4.9(1), printed pp.92--94.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
open NaturalExtensions NaturalExtensions.QuadraticSplitting
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private theorem complement_of_odd_index (N : Subrepresentation ρ) (B : Subgroup G)
    (hodd : Odd B.index) (C : Submodule (ZMod 2) V)
    (hcomp : IsCompl N.toSubmodule C) (hC : B ≤ subspaceStabilizer ρ C) :
    ∃ D : Subrepresentation ρ, IsCompl N.toSubmodule D.toSubmodule := by
  classical
  let p := N.toSubmodule.projectionOnto C hcomp
  have hp (v : N.toSubmodule) : p v = v := Submodule.projectionOnto_apply_left hcomp v
  have hpC (v : V) (hv : v ∈ C) : p v = 0 :=
    (Submodule.projectionOnto_apply_eq_zero_iff hcomp).mpr hv
  have hpB (b : B) (v : V) : p (ρ b v) = N.toRepresentation b (p v) := by
    obtain ⟨n, hn, c, hc, rfl⟩ := Submodule.mem_sup.mp
      ((codisjoint_iff.mp hcomp.codisjoint).symm ▸ Submodule.mem_top (x := v))
    simp only [map_add]
    rw [hpC _ hc, map_zero, add_zero,
      hpC _ ((hC b.property c).2 hc), add_zero]
    exact (hp ⟨ρ b n, N.apply_mem_toSubmodule b hn⟩).trans
      (congrArg (N.toRepresentation b) (hp ⟨n, hn⟩).symm)
  let σ := Representation.linHom ρ N.toRepresentation
  have hpfix (b : B) : σ b p = p := by
    apply LinearMap.ext
    intro v
    change N.toRepresentation b (p (ρ (b : G)⁻¹ v)) = p v
    rw [hpB ⟨(b : G)⁻¹, B.inv_mem b.property⟩]
    change (N.toRepresentation (b : G) * N.toRepresentation (b : G)⁻¹) (p v) = p v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  let : B.FiniteIndex := ⟨by obtain ⟨n, hn⟩ := hodd; omega⟩
  let := Fintype.ofFinite (G ⧸ B)
  let f : G ⧸ B → (V →ₗ[ZMod 2] N.toSubmodule) := fun q => σ q.out p
  have hf (g : G) : f (QuotientGroup.mk g) = σ g p := by
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul B g
    change σ (QuotientGroup.mk g : G ⧸ B).out p = _
    rw [hb, map_mul, Module.End.mul_apply, hpfix b]
  have hcov (g : G) (q : G ⧸ B) : f (g • q) = σ g (f q) := by
    induction q using Quotient.inductionOn with
    | h a =>
      change f (QuotientGroup.mk (g * a)) = _
      rw [hf, hf, map_mul, Module.End.mul_apply]
  let q : V →ₗ[ZMod 2] N.toSubmodule := ∑ x, f x
  have hq (g : G) : σ g q = q := by
    change σ g (∑ x, f x) = ∑ x, f x
    rw [map_sum]
    simp_rw [← hcov]
    exact Equiv.sum_comp (MulAction.toPerm g) f
  have hqeq (g : G) (v : V) : q (ρ g v) = N.toRepresentation g (q v) := by
    have he := LinearMap.congr_fun (hq g) (ρ g v)
    change N.toRepresentation g (q (ρ g⁻¹ (ρ g v))) = q (ρ g v) at he
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at he
    exact he.symm
  have hqN (v : N.toSubmodule) : q v = v := by
    have hconj (g : G) : (σ g p) v = v := by
      change N.toRepresentation g (p (ρ g⁻¹ v)) = v
      rw [show p (ρ g⁻¹ v) = N.toRepresentation g⁻¹ v from
        hp (N.toRepresentation g⁻¹ v)]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    change (∑ x : G ⧸ B, f x) v = v
    rw [LinearMap.sum_apply]
    simp_rw [show ∀ x : G ⧸ B, f x v = v from fun x => hconj x.out]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (ZMod 2)]
    have hc : (Fintype.card (G ⧸ B) : ZMod 2) = 1 := by
      have ho : Odd (Fintype.card (G ⧸ B)) := by
        simpa only [Subgroup.index, Nat.card_eq_fintype_card] using hodd
      obtain ⟨n, hn⟩ := ho
      rw [hn]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
    rw [hc, one_smul]
  let D : Subrepresentation ρ := ⟨q.ker, by
    intro g v hv
    change q (ρ g v) = 0
    rw [hqeq, show q v = 0 from hv, map_zero]⟩
  exact ⟨D, LinearMap.isCompl_of_proj hqN⟩

variable {F : BinaryField} {n : ℕ}

/-- The complete corrected B.4.9(1) splitting implication. -/
theorem doubleNatural_splits (d : DoubleNatural F n ρ)
    (h : SourceHypotheses d) : d.Splits := by
  classical
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  obtain ⟨E, hE, hquad, hroot⟩ := h.four
  obtain ⟨m, j, hEQ⟩ := Marking.exists_marked_axis d h.family hE
  have hQ := m.axis_quadratic_of_source j h E hE hEQ hroot hquad
  have hn : 3 ≤ n := by rcases h.family with he | ⟨_, he⟩ <;> omega
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨i, hij⟩ := exists_ne j
  have hf : m.FixedLifts j := by
    rcases h.family with hn3 | ⟨hF, hn4⟩
    · subst n
      exact LeviLifts.fixed_lifts_rank_one m hij hQ
    · exact LeviLifts.fixed_lifts_binary m hij hF hn4 hQ
  have hl : ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.K j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
    by_cases hF : F.degree = 1
    · obtain ⟨v, hv, hc⟩ := m.binary_coordinate_complement j hF (by omega) hQ hf
      exact ⟨_, hc, localSpace_invariant ρ (m.Q j) hQ v (m.K j)
        (m.K_normalizes_Q j) (fun g hg => hv ⟨g, hg⟩)⟩
    · exact largeField_sourceFamily_complement m j h.family
        (by have hp := F.degree_pos; omega) hQ hf
  obtain ⟨C, hc, hstable⟩ := hl
  obtain ⟨T, hT⟩ := m.exists_sylow_le_K_sup_Q j
  have ho : Odd (m.K j ⊔ m.Q j).index := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact T.not_dvd_index (he.two_dvd.trans (Subgroup.index_dvd_of_le hT))
  exact complement_of_odd_index d.space (m.K j ⊔ m.Q j) ho C hc hstable

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion

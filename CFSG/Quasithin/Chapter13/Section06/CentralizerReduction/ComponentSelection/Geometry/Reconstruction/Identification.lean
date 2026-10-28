module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Family
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Reconstruction.Model

/-!
# Identifying and reconstructing the marked module

The cubic in the literal two-residual of C_L(v) supplies the three singular
vectors spanning v's polar hyperplane. Conversely the stabilizer preserves
the polar form, so its seed span lies in that hyperplane. The finite model
then shows every vector lies in a hyperplane indexed by a nonsingular vector
of this actual V_v, and hence these hyperplanes generate V.

Source: Aschbacher–Smith, combined manuscript, printed pp.926 and 928,
the setup of §13.6 and the reduction immediately before 13.6.8.
-/

public section

open Subgroup BinaryPermutation.FiveCentralizerGeometry
open BinaryPermutation.FiveGeometry
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G] {L V : Subgroup G}
namespace Reconstruction

theorem L_normalizes (s : A5Module.Marking L V) : L ≤ normalizer (V : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl x hx
  obtain ⟨t, rfl⟩ := s.range_eq.ge hx
  exact s.range_eq.le ⟨Multiplicative.ofAdd (act (s.action ⟨l, hl⟩) t.toAdd),
    (s.equivariant ⟨l, hl⟩ t.toAdd).symm⟩

theorem stabilizer_normalizes_perp (s : A5Module.Marking L V) (u : Space) :
    L ⊓ Gv (s.map (Multiplicative.ofAdd u)) ≤ normalizer (vectorPerp s u : Set G) := by
  apply le_normalizer_iff.mpr
  rintro l hl x ⟨t, ht, rfl⟩
  have hfix : act (s.action ⟨l, hl.1⟩) u = u := by
    apply_fun Multiplicative.ofAdd
    apply s.injective
    rw [← s.equivariant]
    change l * s.map (Multiplicative.ofAdd u) * l⁻¹ = _
    rw [mem_centralizer_singleton_iff.mp hl.2]
    simp [mul_assoc]
  refine ⟨Multiplicative.ofAdd (act (s.action ⟨l, hl.1⟩) t.toAdd), ?_,
    (s.equivariant ⟨l, hl.1⟩ t.toAdd).symm⟩
  change form.polarBilin u (act (s.action ⟨l, hl.1⟩) t.toAdd) = 0
  have hp := Model.polar_act (s.action ⟨l, hl.1⟩) u t.toAdd
  rw [hfix] at hp
  exact hp.trans ht

end Reconstruction

theorem Vv_eq_vectorPerp [Finite G] (s : A5Module.Marking L V) :
    Vv L (A5Module.markedZ s) (A5Module.markedV s) = vectorPerp s v := by
  apply le_antisymm
  · apply conjugateSpanBy_le
    · apply zpowers_le.mpr
      exact ⟨Multiplicative.ofAdd z, (by change form.polarBilin v z = 0; decide), rfl⟩
    · apply le_trans ?_ (Reconstruction.stabilizer_normalizes_perp s v)
      rintro x ⟨c, _, rfl⟩
      exact c.property
  · obtain ⟨c, hc, he⟩ := A5Module.exists_residual_cubic s
    have hcG : (c : G) ∈ Lv L (A5Module.markedV s) := ⟨c, hc, rfl⟩
    have he2 : s.action (inclusion inf_le_left (c ^ 2)) = cubic ^ 2 := by
      rw [map_pow, map_pow, he]
    have hm0 := z_mem_Vv L (A5Module.markedZ s) (A5Module.markedV s)
    have hm1 : s.map (Multiplicative.ofAdd (act cubic z)) ∈
        Vv L (A5Module.markedZ s) (A5Module.markedV s) := by
      rw [← he, ← s.equivariant]
      exact subset_closure ⟨(c : G), hcG, _, mem_zpowers _, rfl⟩
    have hm2 : s.map (Multiplicative.ofAdd (act (cubic ^ 2) z)) ∈
        Vv L (A5Module.markedZ s) (A5Module.markedV s) := by
      rw [← he2, ← s.equivariant]
      exact subset_closure ⟨(c : G) ^ 2, pow_mem hcG 2, _, mem_zpowers _, rfl⟩
    rintro x ⟨t, ht, rfl⟩
    obtain ⟨i,j,k,hx⟩ := Reconstruction.Model.span_certificate t.toAdd ht
    have hh (b : Bool) (y : Space)
        (hy : s.map (Multiplicative.ofAdd y) ∈
          Vv L (A5Module.markedZ s) (A5Module.markedV s)) :
        s.map (Multiplicative.ofAdd (if b then y else 0)) ∈
          Vv L (A5Module.markedZ s) (A5Module.markedV s) := by
      cases b
      · exact s.map.map_one ▸ one_mem _
      · exact hy
    change s.map (Multiplicative.ofAdd t.toAdd) ∈ _
    rw [hx]
    change s.map ((Multiplicative.ofAdd (if i then z else 0) *
      Multiplicative.ofAdd (if j then act cubic z else 0)) *
      Multiplicative.ofAdd (if k then act (cubic ^ 2) z else 0)) ∈ _
    rw [map_mul, map_mul]
    exact mul_mem (mul_mem (hh i z hm0) (hh j _ hm1)) (hh k _ hm2)

theorem nonsingularFamily_sSup_eq [Finite G] (s : A5Module.Marking L V) :
    sSup (nonsingularFamily s) = V := by
  apply le_antisymm (nonsingularFamily_le s)
  intro x hx
  obtain ⟨t, rfl⟩ := s.range_eq.ge hx
  obtain ⟨u, hq, hvu, hut⟩ := Reconstruction.Model.family_covers t.toAdd
  apply le_sSup (s := nonsingularFamily s) (a := vectorPerp s u)
  · refine ⟨u, ?_, hq, rfl⟩
    rw [Vv_eq_vectorPerp s]
    exact ⟨Multiplicative.ofAdd u, hvu, rfl⟩
  · exact ⟨t, hut, rfl⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection

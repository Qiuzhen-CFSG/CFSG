module

public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Burnside fusion in weakly closed abelian subgroups

If an abelian subgroup A is weakly closed in a Sylow p-subgroup, N_G(A)
controls element fusion in A. Two copies of A centralize the target element.
Place them in Sylow subgroups of that centralizer and conjugate those Sylow
subgroups there. Weak closure identifies the corrected copies of A, while
the centralizer correction preserves the element being fused.

This is the element form of Aschbacher–Smith, A.1.35, combined manuscript
of 1 March 2004. The subgroup form of this argument also appears in the
project's Chapter16 Bender/GeometryConstruction/Fusion development.
-/

namespace Sylow
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem abelianFusion_weakClosure_other_sylow {T S : Sylow p G} {A : Subgroup G}
    (hweak : ∀ g : G, A.conjBy g ≤ (T : Subgroup G) → A.conjBy g = A)
    (hAS : A ≤ (S : Subgroup G)) {g : G} (hg : A.conjBy g ≤ (S : Subgroup G)) :
    A.conjBy g = A := by
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq G S T
  have hAs : A.conjBy s = A := hweak s (by
    rw [← hs]
    exact map_mono hAS)
  have hAgs : (A.conjBy g).conjBy s = A := by
    rw [conjBy_conjBy]
    apply hweak
    rw [conjBy_mul, ← hs]
    exact map_mono hg
  have he := congrArg (fun H : Subgroup G => H.conjBy s⁻¹) (hAgs.trans hAs.symm)
  simpa only [conjBy_inv] using he

/-- Burnside's fusion lemma for elements of a weakly closed abelian subgroup. -/
public theorem normalizer_fuses_of_abelian_weakly_closed (T : Sylow p G)
    (A : Subgroup G) [IsMulCommutative A] (hAT : A ≤ (T : Subgroup G))
    (hweak : ∀ g : G, A.conjBy g ≤ (T : Subgroup G) → A.conjBy g = A)
    {x y : G} (hx : x ∈ A) (hy : y ∈ A) (hxy : IsConj x y) :
    ∃ n ∈ normalizer (A : Set G), MulAut.conj n x = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  let C := centralizer ({y} : Set G)
  have hAC : A ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (A.le_centralizer hy a ha)
  have hAgC : A.conjBy g ≤ C := by
    rintro a ⟨b, hb, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (MulAut.conj g) (A.le_centralizer hx b hb)
    change (MulAut.conj g b) * y = y * (MulAut.conj g b)
    simpa only [map_mul, show MulAut.conj g x = y from hg] using he
  have hpA := T.isPGroup'.of_injective (inclusion hAT) (inclusion_injective hAT)
  have hpAg : IsPGroup p (A.conjBy g) := hpA.map _
  obtain ⟨P, hP⟩ := (hpA.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨Q, hQ⟩ := (hpAg.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q P
  have hmap : ((A.conjBy g).subgroupOf C).map (MulAut.conj c).toMonoidHom ≤
      (P : Subgroup C) := by
    rw [← hc]
    exact map_mono hQ
  have hcomp : C.subtype.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (c : G)).toMonoidHom.comp C.subtype := by ext a; rfl
  have hconj := map_mono (f := C.subtype) hmap
  rw [map_map, hcomp, ← map_map, map_subgroupOf_eq_of_le hAgC] at hconj
  have hAP : A ≤ (P : Subgroup C).map C.subtype := by
    rw [← map_subgroupOf_eq_of_le hAC]
    exact map_mono hP
  obtain ⟨S, hS⟩ := (P.isPGroup'.map C.subtype).exists_le_sylow
  have he : A.conjBy ((c : G) * g) = A := by
    apply abelianFusion_weakClosure_other_sylow hweak (hAP.trans hS)
    rw [conjBy_mul]
    exact hconj.trans hS
  refine ⟨(c : G) * g, mem_normalizer_iff_map_conj_eq.mpr he, ?_⟩
  change (↑c * g) * x * (↑c * g)⁻¹ = y
  calc
    (↑c * g) * x * (↑c * g)⁻¹ = ↑c * (g * x * g⁻¹) * (↑c)⁻¹ := by group
    _ = ↑c * y * (↑c)⁻¹ := by rw [hg]
    _ = y := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property)

end Sylow

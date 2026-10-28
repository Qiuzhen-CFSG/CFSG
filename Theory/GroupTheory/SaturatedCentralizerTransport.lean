module

public import Theory.GroupTheory.SaturatedCentralizer

/-!
# Transport into a saturated element centralizer

A maximal p-subgroup of an element centralizer receives every p-subgroup of
a conjugate element centralizer after adjusting the conjugating element inside
the target centralizer. This is Sylow conjugacy in the target centralizer.

Source motivation: Janko–Thompson (1970), §4, case (c), printed p.392.
-/

open Subgroup

namespace Subgroup

/-- Conjugate a p-subgroup of one element centralizer into a saturated
p-subgroup of a conjugate element centralizer, preserving the element. -/
public theorem exists_conj_into_saturated_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x y : G) (E R : Subgroup G) (hE : IsPGroup p E) (hR : IsPGroup p R)
    (hEx : E ≤ centralizer ({x} : Set G))
    (hRy : R ≤ centralizer ({y} : Set G))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → E ≤ V →
      V ≤ centralizer ({x} : Set G) → V = E)
    (hconj : IsConj y x) :
    ∃ g : G, (MulAut.conj g) y = x ∧ R.map (MulAut.conj g).toMonoidHom ≤ E := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let C := centralizer ({x} : Set G)
  let f := MulAut.conj g
  let U := R.map f.toMonoidHom
  have hUC : U ≤ C := by
    rintro _ ⟨r, hr, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change f r * x = x * f r
    have hfx : f y = x := hg
    simpa only [map_mul, hfx] using
      congrArg f (mem_centralizer_singleton_iff.mp (hRy hr))
  obtain ⟨P, hEP⟩ := (hE.comap_subtype (K := C)).exists_le_sylow
  have hPE : (P : Subgroup C).map C.subtype = E :=
    hmax _ (P.isPGroup'.map _) (by
      rw [← map_subgroupOf_eq_of_le hEx]
      exact map_mono hEP) (map_subtype_le _)
  obtain ⟨Q, hUQ⟩ := ((hR.map f.toMonoidHom).comap_subtype (K := C)).exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq C Q P
  refine ⟨(a : G) * g, ?_, ?_⟩
  · change ((a : G) * g) * y * ((a : G) * g)⁻¹ = x
    calc
      _ = (a : G) * (g * y * g⁻¹) * (a : G)⁻¹ := by group
      _ = (a : G) * x * (a : G)⁻¹ := by rw [hg]
      _ = x := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp a.property)
  · rintro _ ⟨r, hr, rfl⟩
    have hrU : f r ∈ U := mem_map_of_mem _ hr
    have haP : (MulAut.conj a) (⟨f r, hUC hrU⟩ : C) ∈ P := by
      rw [← ha]
      exact mem_map_of_mem _ (hUQ hrU)
    have hm := mem_map_of_mem C.subtype haP
    rw [hPE] at hm
    change (↑a * (g * r * g⁻¹) * (↑a)⁻¹) ∈ E at hm
    change (↑a * g) * r * (↑a * g)⁻¹ ∈ E
    simpa only [mul_inv_rev, mul_assoc] using hm

end Subgroup

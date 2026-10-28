module

public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.Basic
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Maximal
/-!
# The fixed heptad of every M23 involution

Exhaustive involution fusion transports the representative's seven fixed
points to a heptad for each involution. Its centralizer preserves this actual
finite set, whose stabilizer is an ordinary maximal subgroup. These two
subgroups are kept distinct.

Source: Aschbacher–Smith, 2.3.9(7)(f), printed pp.525–526, and 5.2.21,
printed p.657, combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Sporadic.Mathieu
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry

/-- The actual fixed points in the natural permutation action. For an involution,
this finite set is a heptad. -/
noncomputable def fixedHeptad (t : M23) : Finset (Fin 23) :=
  Finset.univ.filter (fun a => t • a = a)

@[simp] theorem mem_fixedHeptad (t : M23) (a : Fin 23) :
    a ∈ fixedHeptad t ↔ t • a = a := by simp [fixedHeptad]

theorem fixedHeptad_conj (g t : M23) :
    fixedHeptad (MulAut.conj g t) = g • fixedHeptad t := by
  ext a
  rw [mem_fixedHeptad, Finset.mem_smul_finset]
  constructor
  · intro ha
    refine ⟨g⁻¹ • a, (mem_fixedHeptad _ _).mpr ?_, smul_inv_smul _ _⟩
    have ha' := congrArg (fun a : Fin 23 => g⁻¹ • a) ha
    simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using ha'
  · rintro ⟨b, hb, rfl⟩
    rw [mem_fixedHeptad] at hb
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, hb]

theorem fixedHeptad_involutionRepresentative :
    fixedHeptad involutionRepresentative = involutionHeptad := by
  ext a
  exact (mem_fixedHeptad _ _).trans (involutionRepresentative_fixed_iff a)

/-- Exhaustive involution fusion proves that the fixed points form a Witt heptad. -/
theorem fixedHeptad_mem {t : M23} (ht : orderOf t = 2) : fixedHeptad t ∈ m23Blocks := by
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (involutions_isConj involutionRepresentative t involutionRepresentative_order ht)
  have hg' : MulAut.conj g involutionRepresentative = t := hg
  rw [← hg', fixedHeptad_conj, fixedHeptad_involutionRepresentative]
  exact smul_heptad g involutionHeptad_mem

/-- Commuting permutations preserve the entire fixed-point heptad. This supplies
only centralizer containment, not containment of the stabilizer in a local M. -/
theorem centralizer_le_fixedHeptad_stabilizer (t : M23) :
    centralizer ({t} : Set M23) ≤ MulAction.stabilizer M23 (fixedHeptad t) := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro a ha
  rw [mem_fixedHeptad] at ha ⊢
  have hc : g * t = t * g := mem_centralizer_singleton_iff.mp hg
  calc
    t • (g • a) = (t * g) • a := (mul_smul _ _ _).symm
    _ = (g * t) • a := by rw [hc]
    _ = g • a := by rw [mul_smul, ha]

/-- The stabilizer of an involution's fixed heptad is an ordinary maximal subgroup. -/
theorem fixedHeptad_stabilizer_isCoatom {t : M23} (ht : orderOf t = 2) :
    IsCoatom (MulAction.stabilizer M23 (fixedHeptad t)) :=
  heptad_stabilizer_isCoatom (fixedHeptad_mem ht)

/-- Simplicity and the proper fixed-heptad stabilizer give centerlessness. -/
theorem m23_center_eq_bot : center M23 = ⊥ := by
  let := m23_isSimpleGroup
  rcases (inferInstance : (center M23).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply (fixedHeptad_stabilizer_isCoatom involutionRepresentative_order).ne_top
    apply top_unique
    intro g _
    apply centralizer_le_fixedHeptad_stabilizer
    apply mem_centralizer_singleton_iff.mpr
    have hg : g ∈ center M23 := by rw [h]; trivial
    exact (mem_center_iff.mp hg involutionRepresentative).symm

end Sporadic.Mathieu.M23Geometry

end

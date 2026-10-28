module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.TwoCore
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The small-degree obstruction for a marked natural component

The explicit unitriangular element with coordinates (1,1,0) has order four.
In degree at most two in characteristic two, a fourth-power-one operator
has square one: the kernels of powers of its nilpotent difference from the
identity stabilize by the dimension. The natural seed's actual group
isomorphism transports the element into the source component. Its square
lies in the kernel of any such small representation; quasisimplicity and
the already proved trivial center force that kernel to be the whole group.

This supplies the model-specific obstruction for the commutant calculation
in Aschbacher–Smith, B.5.9, printed p.108 (1 March 2004 manuscript).
It does not assume simplicity of an unrelated model or semisimplicity of W.
The existing unitriangular realization and its attribution are retained in
`Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic`.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false

/-- In characteristic two, degree at most two excludes order four, including degree zero. -/
theorem square_eq_one_of_fourth_eq_one {E X : Type*} [Field E] [CharP E 2] [AddCommGroup X] [Module E X]
    [Module.Finite E X] (T : Module.End E X) (hd : Module.finrank E X ≤ 2)
    (h4 : T ^ 4 = 1) : T ^ 2 = 1 := by
  rcases subsingleton_or_nontrivial X with h | h
  · let := h
    exact Subsingleton.elim _ _
  let := h
  let : CharP (Module.End E X) 2 :=
    charP_of_injective_algebraMap (algebraMap E (Module.End E X)).injective 2
  have hn : (T - 1) ^ 4 = 0 := by
    have h := sub_pow_char_pow_of_commute (p := 2) (n := 2) (Commute.one_right T)
    simpa only [show 2 ^ 2 = 4 by decide, one_pow, h4, sub_self] using h
  have hk : LinearMap.ker ((T - 1) ^ 2) = ⊤ := by
    rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le hd,
      ← Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := T - 1) (m := 4) (by omega), hn]
    exact LinearMap.ker_zero
  have h2 : (T - 1) ^ 2 = 0 := LinearMap.ker_eq_top.mp hk
  rw [sub_pow_char_of_commute (p := 2) (Commute.one_right T), one_pow] at h2
  exact sub_eq_zero.mp h2

open Matrix.PSL3Even.UnipotentGeometry in
/-- The literal upper-unitriangular SL₃ model contains an element of order four. -/
theorem sl3_order_four {F : Type*} [Field F] [CharP F 2] :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) F, g ^ 4 = 1 ∧ g ^ 2 ≠ 1 := by
  let u : U F := ⟨1, 1, 0⟩
  have h4 : u ^ 4 = 1 := by
    change u ^ (2 * 2) = 1
    rw [pow_mul]
    apply (square_eq_one_iff F (u ^ 2)).mpr
    left
    simp [pow_two, u, CharTwo.add_self_eq_zero]
  have h2 : u ^ 2 ≠ 1 := by
    intro he
    have h := (Matrix.PSL3Even.UnipotentGeometry.square_eq_one_iff F u).mp he
    simp [u] at h
  refine ⟨specialLinear F u, ?_, ?_⟩
  · rw [← map_pow, h4, map_one]
  · intro he
    apply h2
    apply specialLinear_injective F
    simpa only [map_pow, map_one] using he

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The actual natural component has no nontrivial characteristic-two representation of degree at most two. -/
theorem seed_small_degree {A L : Subgroup G}
    (seed : NaturalSeed ρ A L) (hL : IsComponent G L)
    {E X : Type*} [Field E] [CharP E 2] [AddCommGroup X] [Module E X]
    [Module.Finite E X] (σ : Representation E L X)
    (hd : Module.finrank E X ≤ 2) : σ = 1 := by
  let : IsQuasisimple L := hL.2
  obtain ⟨u, h4, h2⟩ := sl3_order_four (F := seed.field.Carrier)
  let l : L := seed.natural.groupEquiv.symm u
  have hl4 : l ^ 4 = 1 := by
    change (seed.natural.groupEquiv.symm u) ^ 4 = 1
    rw [← map_pow, h4, map_one]
  have hl2 : l ^ 2 ≠ 1 := by
    intro he
    apply h2
    have hh := congrArg seed.natural.groupEquiv he
    simpa only [l, map_pow, map_one, MulEquiv.apply_symm_apply] using hh
  have hs2 : σ l ^ 2 = 1 := square_eq_one_of_fourth_eq_one _ hd (by
    rw [← map_pow, hl4, map_one])
  rcases IsQuasisimple.normal_le_center_or_eq_top σ.ker with hc | ht
  · have hmem : l ^ 2 ∈ σ.ker := by
      change σ (l ^ 2) = 1
      rwa [map_pow]
    have he : l ^ 2 ∈ center L := hc hmem
    rw [seed_center_eq_bot ρ seed, mem_bot] at he
    exact (hl2 he).elim
  · exact MonoidHom.ker_eq_top_iff.mp ht

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors

module

public import Theory.SpecificGroups.GL2.SemidihedralSylow
public import Theory.Mathieu.M11.Properties.Centralizer

/-!
# An actual semidihedral Sylow two-subgroup of M11

The established equivalence C_M11(z) ≃ GL₂(3) embeds a Sylow two-subgroup
of GL₂(3) into M11. Its order is sixteen, the full two-part of |M11| = 7920,
so the image is Sylow in M11. The induced subgroup equivalence transports
the semidihedral generators, their orders and relation, and generation.

This supplies the concrete Sylow model used for condition E in
Aschbacher–Smith, Theorem 0.1.2(5), printed pp.3–4. The GL₂ Sylow theorem
contains the explicit quadratic-torus construction and its source reference.
-/

namespace Sporadic.Mathieu
open Subgroup

/-- M11 has a Sylow two-subgroup with the full SD16 presentation. -/
public theorem m11_exists_semidihedral_sylow :
    ∃ (T : Sylow 2 M11) (a b : T), orderOf a = 8 ∧ orderOf b = 2 ∧
      b * a * b⁻¹ = a ^ 3 ∧ closure ({a, b} : Set T) = ⊤ := by
  obtain ⟨P, n, _, hp, a, b, ha, hb, hc, hg, -, -⟩ :=
    Matrix.GeneralLinearGroup.exists_semidihedral_sylow (ZMod 3) (by norm_num)
  have hPcard : Nat.card P = 16 := by
    rw [P.card_eq_multiplicity, Matrix.card_GL_field]
    norm_num [Fin.prod_univ_two]
    decide +kernel
  have hn4 : n = 4 := by
    have h : 2 ^ n = 2 ^ 4 := hp.symm.trans hPcard
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) h
  subst n
  norm_num at ha hc
  let f : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) →* M11 :=
    m11InvolutionCentralizer.subtype.comp m11InvolutionCentralizer_mulEquiv_gl2.symm.toMonoidHom
  have hf : Function.Injective f :=
    m11InvolutionCentralizer.subtype_injective.comp
      m11InvolutionCentralizer_mulEquiv_gl2.symm.injective
  let S := (P : Subgroup _).map f
  let e : P ≃* S := Subgroup.equivMapOfInjective _ f hf
  have hS : Nat.card S = 16 := (Nat.card_congr e.toEquiv).symm.trans hPcard
  let T : Sylow 2 M11 := Sylow.ofCard S (by rw [hS, m11_order]; decide +kernel)
  refine ⟨T, e a, e b, ?_, ?_, ?_, ?_⟩
  · exact (e.orderOf_eq a).trans ha
  · exact (e.orderOf_eq b).trans hb
  · change e b * e a * (e b)⁻¹ = (e a) ^ 3
    rw [← map_inv, ← map_mul, ← map_mul, hc, map_pow]
    rfl
  · change closure ({e a, e b} : Set S) = ⊤
    have hh := congrArg (Subgroup.map e.toMonoidHom) hg
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hh
    convert hh using 1
    rfl
end Sporadic.Mathieu

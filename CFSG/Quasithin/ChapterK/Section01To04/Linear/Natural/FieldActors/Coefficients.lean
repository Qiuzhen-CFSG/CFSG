module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Context
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldDisplacement
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.CharP.Two

/-!
# Coefficient involutions in the natural SL₃ branch

The recognized binary intertwiner transports the ambient action to its actual
natural coordinates. Its scalar equation defines a homomorphism to the field
automorphisms. A linear involution has determinant one in characteristic two,
and faithfulness identifies it with an element of the marked SL₃ layer.
Consequently an outer involution has a nontrivial coefficient involution, and
semilinear descent gives its displacement on the original module.

Source: Aschbacher–Smith, K.3.2.1, printed pp.454–455 (1 March 2004).
-/

@[expose] public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (F : BinaryField)
  (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))

/-- The ambient action in the recognized natural coordinates. -/
noncomputable def coordinateAction : Representation (ZMod 2) G (Fin 3 → F.Carrier) :=
  e.linearEquiv.conjRingEquiv.toMonoidHom.comp ρ

lemma coordinateAction_apply (g : G) (v : Fin 3 → F.Carrier) :
    coordinateAction ρ L F e g v = e.linearEquiv (ρ g (e.linearEquiv.symm v)) := rfl

lemma coordinateAction_intertwines (g : G) (v : V) :
    e.linearEquiv (ρ g v) = coordinateAction ρ L F e g (e.linearEquiv v) := by
  rw [coordinateAction_apply, e.linearEquiv.symm_apply_apply]

lemma coordinateAction_faithful (hf : Function.Injective ρ) :
    Function.Injective (coordinateAction ρ L F e) :=
  e.linearEquiv.conjRingEquiv.injective.comp hf

lemma coordinateAction_natural (g : L) (v : Fin 3 → F.Carrier) :
    coordinateAction ρ L F e g v = (e.groupEquiv g).val.mulVec v := by
  have he := e.intertwines g (e.linearEquiv.symm v)
  rw [e.linearEquiv.apply_symm_apply] at he
  exact he

lemma coordinateAction_semilinear (hs : IsSemilinearExtension ρ L F 3 e) :
    ∀ g : G, ∃ σ : F.Carrier ≃+* F.Carrier,
      ∀ (c : F.Carrier) (v : Fin 3 → F.Carrier), coordinateAction ρ L F e g (c • v) =
        σ c • coordinateAction ρ L F e g v := by
  intro g
  obtain ⟨σ, hσ⟩ := hs g
  refine ⟨σ, fun c v => ?_⟩
  have he := hσ c (e.linearEquiv.symm v)
  rw [e.linearEquiv.apply_symm_apply] at he
  exact he

/-- The genuine coefficient homomorphism of the recognized ambient action. -/
noncomputable def coefficientAction (hs : IsSemilinearExtension ρ L F 3 e) :
    G →* (F.Carrier ≃+* F.Carrier) :=
  SL3OddNaturalNormalizer.fieldAction (coordinateAction ρ L F e)
    (coordinateAction_semilinear ρ L F e hs)

lemma coefficientAction_smul (hs : IsSemilinearExtension ρ L F 3 e)
    (g : G) (c : F.Carrier) (v : Fin 3 → F.Carrier) :
    coordinateAction ρ L F e g (c • v) =
      coefficientAction ρ L F e hs g c • coordinateAction ρ L F e g v :=
  SL3OddNaturalNormalizer.fieldAction_smul _ _ _ _ _

lemma coefficientAction_eq_one_iff (hs : IsSemilinearExtension ρ L F 3 e) (g : G) :
    coefficientAction ρ L F e hs g = 1 ↔
      ∀ (c : F.Carrier) (v : Fin 3 → F.Carrier), coordinateAction ρ L F e g (c • v) = c • coordinateAction ρ L F e g v :=
  SL3OddNaturalNormalizer.fieldAction_eq_one_iff _ _ _

lemma component_le_coefficientAction_ker (hs : IsSemilinearExtension ρ L F 3 e) :
    L ≤ (coefficientAction ρ L F e hs).ker := by
  intro g hg
  apply (coefficientAction_eq_one_iff ρ L F e hs g).mpr
  intro c v
  change coordinateAction ρ L F e (⟨g, hg⟩ : L) (c • v) =
    c • coordinateAction ρ L F e (⟨g, hg⟩ : L) v
  rw [coordinateAction_natural, coordinateAction_natural, Matrix.mulVec_smul]

/-- In characteristic two a linear actor with square one belongs to the marked
special linear layer. This uses the determinant and the actual faithful action. -/
theorem linear_square_one_mem_component (hf : Function.Injective ρ)
    (a : G) (ha : a ^ 2 = 1)
    (hl : ∀ (c : F.Carrier) (v : Fin 3 → F.Carrier), coordinateAction ρ L F e a (c • v) =
      c • coordinateAction ρ L F e a v) : a ∈ L := by
  let τ := coordinateAction ρ L F e
  let t : Module.End F.Carrier (Fin 3 → F.Carrier) :=
    { toFun := τ a
      map_add' := (τ a).map_add
      map_smul' := hl }
  have ht : t ^ 2 = 1 := by
    apply LinearMap.ext
    intro v
    change τ a (τ a v) = v
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ha, map_one]
    rfl
  have hd : LinearMap.det t = 1 := by
    have hd2 : LinearMap.det t ^ 2 = 1 := by
      rw [← map_pow, ht, map_one]
    rcases sq_eq_one_iff.mp hd2 with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  let m : Matrix.SpecialLinearGroup (Fin 3) F.Carrier :=
    ⟨LinearMap.toMatrix' t, (LinearMap.det_toMatrix' t).trans hd⟩
  have he : a = (e.groupEquiv.symm m : L) := by
    apply coordinateAction_faithful ρ L F e hf
    apply LinearMap.ext
    intro v
    rw [coordinateAction_natural, e.groupEquiv.apply_symm_apply]
    change t v = (LinearMap.toMatrix' t).mulVec v
    exact (LinearMap.toMatrix'_mulVec t v).symm
  exact he ▸ (e.groupEquiv.symm m).property

/-- An outer square-one actor has genuinely nontrivial coefficient action. -/
theorem outer_coefficient_ne_one (hf : Function.Injective ρ)
    (hs : IsSemilinearExtension ρ L F 3 e) (a : G) (ha : a ^ 2 = 1) (haL : a ∉ L) :
    coefficientAction ρ L F e hs a ≠ 1 := by
  intro he
  exact haL (linear_square_one_mem_component ρ L F e hf a ha
    ((coefficientAction_eq_one_iff ρ L F e hs a).mp he))

/-- The coefficient automorphism of an outer involution has order exactly two. -/
theorem outer_coefficient_orderOf (hf : Function.Injective ρ)
    (hs : IsSemilinearExtension ρ L F 3 e) (a : G) (ha : orderOf a = 2) (haL : a ∉ L) :
    orderOf (coefficientAction ρ L F e hs a) = 2 := by
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  exact orderOf_eq_prime (by rw [← map_pow, ha2, map_one])
    (outer_coefficient_ne_one ρ L F e hf hs a ha2 haL)

/-- The outer involution's source displacement, on the original binary module. -/
theorem outer_involution_fixedCodim (hf : Function.Injective ρ)
    (hs : IsSemilinearExtension ρ L F 3 e) (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hdegree : F.degree = 2 * s) :
    fixedCodim ρ (Subgroup.zpowers a) = 3 * s := by
  apply field_involution_fixedCodim ρ F 3 e.linearEquiv a ha
    (coefficientAction ρ L F e hs a)
    (outer_coefficient_orderOf ρ L F e hf hs a ha haL) _ s hdegree
  intro c v
  simpa only [coordinateAction_apply, e.linearEquiv.symm_apply_apply] using
    coefficientAction_smul ρ L F e hs a c (e.linearEquiv v)

/-- Application retaining all standing source hypotheses. No coefficient-order
or displacement assertion is part of those hypotheses. -/
theorem source_outer_involution_fixedCodim {K : GroupClass}
    (h : SourceInput ρ L F 3 K) (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hdegree : F.degree = 2 * s) :
    fixedCodim ρ (Subgroup.zpowers a) = 3 * s :=
  outer_involution_fixedCodim ρ L F h.natural h.faithful h.semilinear a ha haL s hdegree

end CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors

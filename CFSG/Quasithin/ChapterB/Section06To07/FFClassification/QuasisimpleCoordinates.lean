module
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource
/-!
# The original moved section gives literal subgroup quotient coordinates

Identify the B.5.1 moved subspace with the original elementary subgroup
commutator, using the actual quotient image of its actor. Composing this
identity with the stored central quotient and natural intertwiner gives a
surjective linear map. Its kernel is exactly the original relative centralizer,
and its equivariance uses literal ambient conjugation.

Source: Aschbacher–Smith B.6.9–10 and E.2.3, pp.115–117 and216–217.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G H D M : Type*} [Group G] [Group H] [Group D]
  [AddCommGroup M] [Module (ZMod 2) M]
  (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
  (q : G →* H) (hq : Function.Surjective q) (hker : q.ker = centralizer (U : Set G))
  (Y : Subgroup H) (A : Subgroup Y)
  (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp Y.subtype) A)
  (X : Subgroup G) [IsElementaryAbelian 2 (⁅U,X⁆ : Subgroup G)]
  (hX : A.map Y.subtype = X.map q)

include hX in
omit [IsElementaryAbelian 2 (⁅U,X⁆ : Subgroup G)] in
theorem source_moved_space_eq :
    s.space.toSubmodule =
      subspaceCommutator (NormalElementaryQuotient.representation U q hq hker) ⊤ (X.map q) := by
  rw [s.space_eq]
  have hh := subspaceCommutator_map_embedding
    ((NormalElementaryQuotient.representation U q hq hker).comp Y.subtype)
    (NormalElementaryQuotient.representation U q hq hker) Y.subtype
    (LinearMap.id : Additive U →ₗ[ZMod 2] Additive U) (fun _ _ => rfl) A ⊤
  simpa only [Submodule.map_id,hX] using hh

noncomputable def sourceMovedSubgroupEquiv :
    Additive (⁅U,X⁆ : Subgroup G) ≃ₗ[ZMod 2] s.space.toSubmodule :=
  (NormalElementaryQuotient.movedEquiv U q hq hker X).trans
    (LinearEquiv.ofEq _ _ (source_moved_space_eq U q hq hker Y A s X hX).symm)

@[simp] theorem sourceMovedSubgroupEquiv_val (v : Additive (⁅U,X⁆ : Subgroup G)) :
    (sourceMovedSubgroupEquiv U q hq hker Y A s X hX v).val =
      Additive.ofMul ⟨v.toMul,(commutator_le_left U X) v.toMul.property⟩ := rfl

variable (τ : Representation (ZMod 2) D M)
  (e : ActionEquiv (s.action.comp A.subtype) τ)
noncomputable def sourceMovedQuotientMap : Additive (⁅U,X⁆ : Subgroup G) →ₗ[ZMod 2] M :=
  e.linearEquiv.toLinearMap.comp (s.central.toSubmodule.mkQ.comp
    (sourceMovedSubgroupEquiv U q hq hker Y A s X hX).toLinearMap)

theorem sourceMovedQuotientMap_surjective :
    Function.Surjective (sourceMovedQuotientMap U q hq hker Y A s X hX τ e) :=
  e.linearEquiv.surjective.comp (s.central.toSubmodule.mkQ_surjective.comp
    (sourceMovedSubgroupEquiv U q hq hker Y A s X hX).surjective)

theorem sourceMovedQuotientMap_kernel (v : Additive (⁅U,X⁆ : Subgroup G)) :
    sourceMovedQuotientMap U q hq hker Y A s X hX τ e v = 0 ↔
      (v.toMul : G) ∈ centralizer (X : Set G) := by
  let w := sourceMovedSubgroupEquiv U q hq hker Y A s X hX v
  change e.linearEquiv (s.central.toSubmodule.mkQ w) = 0 ↔ _
  rw [← e.linearEquiv.map_zero,e.linearEquiv.injective.eq_iff,
    Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,s.central_eq]
  change (∀ a : A, s.space.toRepresentation (a:Y) w = w) ↔ _
  have hf : (∀ a : A, s.space.toRepresentation (a:Y) w = w) ↔
      w.val ∈ fixedSpace (NormalElementaryQuotient.representation U q hq hker) (A.map Y.subtype) := by
    constructor
    · intro h a
      obtain ⟨b,hb,he⟩ := a.property
      change NormalElementaryQuotient.representation U q hq hker (a:H) w.val = w.val
      rw [← he]
      exact congrArg Subtype.val (h ⟨b,hb⟩)
    · intro h a
      exact Subtype.ext (h ⟨(a:Y),mem_map_of_mem Y.subtype a.property⟩)
  rw [hf,hX,NormalElementaryQuotient.mem_fixedSpace_image]
  rfl

variable [X.Normal]
theorem sourceMovedQuotientMap_conjugation (g : G) (a : A) (hga : q g = (a:Y))
    (v : Additive (⁅U,X⁆ : Subgroup G)) :
    sourceMovedQuotientMap U q hq hker Y A s X hX τ e
      (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
      τ (e.groupEquiv a) (sourceMovedQuotientMap U q hq hker Y A s X hX τ e v) := by
  let m := sourceMovedSubgroupEquiv U q hq hker Y A s X hX
  have hequiv : m (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
      s.space.toRepresentation (a:Y) (m v) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    change g*(v.toMul:G)*g⁻¹ =
      ((NormalElementaryQuotient.representation U q hq hker (a:Y)
        (Additive.ofMul ⟨v.toMul,(commutator_le_left U X) v.toMul.property⟩)).toMul:G)
    rw [← hga,NormalElementaryQuotient.representation_apply]
    rfl
  change e.linearEquiv (s.central.toSubmodule.mkQ (m _)) = _
  rw [hequiv]
  exact e.intertwines a (s.central.toSubmodule.mkQ (m v))
end CFSG.Quasithin.ChapterB

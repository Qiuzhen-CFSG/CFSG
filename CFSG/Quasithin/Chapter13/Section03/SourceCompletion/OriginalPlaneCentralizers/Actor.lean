module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Cubic
public import Theory.Representation.G2BinaryNaturalNormalizer

/-!
# The original component image in every full chart

Perfectness puts the component image inside the actual derived G₂ group.
Faithfulness of the compatible chart and the given component equivalence
identify their orders, so the inclusion is equality. In particular the cubic
can be lifted from the original component rather than just the full normalizer.

Source: Aschbacher--Smith 13.3.12, printed p.889.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
variable {G : Type*} [Group G] [Finite G] {V L : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
theorem component_actor_image [Group.IsPerfect L]
    (hLN : L ≤ normalizer (V : Set G))
    (e : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (f : Automizer V →* Atlas.G2.Model K) (E : Additive V ≃ₗ[K] W)
    (he : ∀ a v, E (automizerRepresentation V a v) = rho (f a) (E v)) :
    (inducedAutomizer V L).map f = commutator (Atlas.G2.Model K) := by
  let J := L.subgroupOf (normalizer (V : Set G))
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hLN).symm.surjective
  let : Group.IsPerfect (inducedAutomizer V L) :=
    Group.IsPerfect.map V.normalizerMonoidHom.rangeRestrict
  let : Group.IsPerfect ((inducedAutomizer V L).map f) := Group.IsPerfect.map f
  have hf : Function.Injective f := by
    intro a b hab
    apply automizerRepresentation_injective V
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [he, he, hab]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [← commutator_eq_self (H := (inducedAutomizer V L).map f)]
    exact Subgroup.commutator_mono le_top le_top
  · rw [Subgroup.card_map_of_injective hf,
      Nat.card_congr e.toEquiv]

omit [Finite G] in
/-- Every compatible chart lifts the specified cubic from L itself. -/
theorem exists_component_cubic_lift [Group.IsPerfect L]
    (hLN : L ≤ normalizer (V : Set G))
    (e : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (f : Automizer V →* Atlas.G2.Model K) (E : Additive V ≃ₗ[K] W)
    (he : ∀ a v, E (automizerRepresentation V a v) = rho (f a) (E v))
    (A : Subgroup G) (hAV : A ≤ V) (hA : pointCoordinateSubspace E A = plane) :
    ∃ n : normalizer (V : Set G), n.val ∈ L ∧
      f (V.normalizerMonoidHom.rangeRestrict n) = cubic ∧
      n.val ∈ centralizer (A : Set G) ∧
      n.val ∈ normalizer (perpendicular E : Set G) ∧
      ⁅zpowers n.val, perpendicular E⁆ = perpendicular E := by
  have hd : cubic ∈ (inducedAutomizer V L).map f :=
    (component_actor_image hLN e f E he).symm ▸ cubic_mem_derived
  obtain ⟨a, ⟨n, hnL, rfl⟩, hn⟩ := hd
  refine ⟨n, hnL, hn, ?_, cubic_normalizes_perpendicular f E he n hn,
    perpendicular_commutator f E he n hn⟩
  intro x hx
  let v : Additive V := Additive.ofMul ⟨x, hAV hx⟩
  have hv : E v ∈ plane := hA ▸ (mem_pointCoordinateSubspace E A v).mpr hx
  have hf : automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n) v = v := by
    apply E.injective
    rw [he, hn, cubic_fixes_plane _ hv]
  have hc : n.val * x * n.val⁻¹ = x := congrArg (fun w : Additive V => w.toMul.val) hf
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers

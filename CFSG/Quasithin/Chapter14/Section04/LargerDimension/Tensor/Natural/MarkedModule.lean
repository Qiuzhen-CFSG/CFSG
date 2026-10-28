module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Lifting
public import Theory.Representation.SL2FourNaturalOrbits.PointCommutator
public import Theory.Representation.BinaryOffender.ConjugationImage

/-!
# Applying marked natural-module coordinates to the source X₂

The constituent is embedded in the literal U/Z(U), and the action formula
is conjugation through the actual projection. Its Borel cubic expands Ṽ₂ to
an F₄-point; a marked root in the actual Wᵍ moves onto the same point.
The source hyperplane and [Wᵍ,W]≤E then give containment upstairs, while
extraspecial normal-subgroup theory supplies the central factor in order eight.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma 14.4.10,
printed pp.1010–1011. `Coordinates` is an output contract for the still
required natural tensor geometry. None of these conditional applications
constructs those marks or proves the full source theorem on its own.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural
open Representation.SL2FourNatural
variable {G : Type*} [Group G]

/-- Coordinate output still to be constructed from the source tensor action.
All vectors live in the literal central quotient, and the marked root belongs
to the actual Wᵍ. This is not a replacement for Hypothesis 14.3.10. -/
structure Coordinates (H T U V₂ D Wg : Subgroup G)
    [IsElementaryAbelian 2 (U ⧸ center U)]
    (hn : H ≤ normalizer (U : Set G)) where
  representation : Representation (ZMod 2) H (Additive (U ⧸ center U))
  conjugation : ∀ (h : H) (u : U),
    representation h (Additive.ofMul (QuotientGroup.mk' (center U) u)) =
      Additive.ofMul (QuotientGroup.mk' (center U)
        ⟨(h : G) * u * (h : G)⁻¹, le_normalizer_iff.mp hn h h.property u u.property⟩)
  embedding : V →ₗ[ZMod 2] Additive (U ⧸ center U)
  injective : Function.Injective embedding
  actor : second H T →* SL
  equivariant : ∀ (x : second H T) (v : V),
    representation (inclusion (second_le H T) x) (embedding v) =
      embedding (PointCommutator.representation (actor x) v)
  point_image : binarySubgroup (PointCommutator.point.map embedding) = tilde U V₂
  constituent_image : binarySubgroup embedding.range = tilde U D
  borel_stabilizes : actor.range ≤
    subspaceStabilizer PointCommutator.representation upperFixed
  cubic_mem : PointCommutator.cubic ∈ actor.range
  root : H
  root_mem : (root : G) ∈ Wg
  root_action : ∀ v : V, representation root (embedding v) =
    embedding (PointCommutator.representation (upper 1) v)

variable {H T U V₂ D Wg : Subgroup G}
  [IsElementaryAbelian 2 (U ⧸ center U)] {hn : H ≤ normalizer (U : Set G)}

/-- The actual image [Ṽ₂,X₂] is the calculated F₄-point in the embedded
natural constituent. -/
theorem Coordinates.moved_tilde_eq (c : Coordinates H T U V₂ D Wg hn)
    (hVU : V₂ ≤ U) :
    tilde U (movedSpace V₂ (second H T)) = binarySubgroup (upperFixed.map c.embedding) := by
  have he := commutator_image_eq_of_embedding c.representation PointCommutator.representation
    U V₂ (second H T) ((second_le H T).trans hn) hVU
    (inclusion (second_le H T)) (QuotientGroup.mk' (center U))
    (fun x u => c.conjugation (inclusion (second_le H T) x) u)
    c.embedding c.actor c.equivariant PointCommutator.point c.point_image
  rw [PointCommutator.point_commutator c.actor.range c.borel_stabilizes c.cubic_mem] at he
  exact he

/-- The field point contains the literal image of V₂. -/
theorem Coordinates.point_le_moved_tilde (c : Coordinates H T U V₂ D Wg hn)
    (hVU : V₂ ≤ U) : tilde U V₂ ≤ tilde U (movedSpace V₂ (second H T)) := by
  rw [c.moved_tilde_eq hVU, ← c.point_image]
  intro w hw
  exact Submodule.map_mono (f := c.embedding)
    (show PointCommutator.point ≤ upperFixed from inf_le_left) hw

/-- The image is a genuine field point in the chosen natural constituent,
and contains the original binary point Ṽ₂. -/
theorem Coordinates.moved_tilde_is_field_point (c : Coordinates H T U V₂ D Wg hn)
    (hVU : V₂ ≤ U) :
    (∃ L : Submodule F V, Module.finrank F L = 1 ∧
      binarySubgroup ((L.restrictScalars (ZMod 2)).map c.embedding) =
        tilde U (movedSpace V₂ (second H T))) ∧
    tilde U V₂ ≤ tilde U (movedSpace V₂ (second H T)) ∧
    tilde U (movedSpace V₂ (second H T)) ≤ tilde U D := by
  obtain ⟨L, hL, hLe⟩ := PointCommutator.fieldPoint_isFieldLine
  refine ⟨⟨L, hL, ?_⟩, c.point_le_moved_tilde hVU, ?_⟩
  · rw [hLe, c.moved_tilde_eq hVU]
  · rw [c.moved_tilde_eq hVU, ← c.constituent_image]
    rintro w ⟨v, _, he⟩
    exact ⟨v, he⟩

/-- Injectivity of the constituent coordinates gives order four downstairs. -/
theorem Coordinates.moved_tilde_card (c : Coordinates H T U V₂ D Wg hn)
    (hVU : V₂ ≤ U) : Nat.card (tilde U (movedSpace V₂ (second H T))) = 4 := by
  rw [c.moved_tilde_eq hVU, binarySubgroup_card,
    ← Nat.card_congr (Submodule.equivMapOfInjective c.embedding c.injective upperFixed).toEquiv]
  exact card_upperFixed

/-- The root in the actual Wᵍ moves the full constituent onto its F₄-point. -/
theorem Coordinates.moved_tilde_le_constituent_commutator
    (c : Coordinates H T U V₂ D Wg hn) (hVU : V₂ ≤ U)
    (hDU : D ≤ U) (hWgH : Wg ≤ H) :
    tilde U (movedSpace V₂ (second H T)) ≤ tilde U ⁅D, Wg⁆ := by
  rw [c.moved_tilde_eq hVU]
  have he := commutator_image_eq c.representation U D Wg (hWgH.trans hn) hDU
    (inclusion hWgH) (QuotientGroup.mk' (center U))
    (fun x u => c.conjugation (inclusion hWgH x) u)
    c.embedding.range c.constituent_image
  change _ ≤ (⁅D, Wg⁆.subgroupOf U).map (QuotientGroup.mk' (center U))
  rw [he]
  rintro w ⟨v, hv, hvw⟩
  let z : V := ![0, v 0]
  have hz : PointCommutator.representation (upper 1) z - z = v :=
    PointCommutator.fieldPoint_displacement v hv
  have hm : c.representation c.root (c.embedding z) - c.embedding z ∈
      subspaceCommutator c.representation c.embedding.range (inclusion hWgH).range := by
    apply Submodule.subset_span
    refine ⟨c.root, ?_, c.embedding z, ⟨z, rfl⟩, rfl⟩
    exact ⟨⟨c.root, c.root_mem⟩, Subtype.ext rfl⟩
  rw [c.root_action, ← map_sub, hz, hvw] at hm
  exact hm

/-- Conditional source application. The coordinate producer must supply c;
no order or moved-containment conclusion is part of that coordinate record. -/
theorem Coordinates.second_mem_Y [Finite G] [IsExtraspecial 2 U]
    (c : Coordinates H T U V₂ D Wg hn) {E W : Subgroup G}
    (hX : second H T ∈ XFamily H T) (hUT : U ≤ T) (hVU : V₂ ≤ U)
    (hZV : center U ≤ V₂.subgroupOf U) (hZE : center U ≤ E.subgroupOf U)
    (hDU : D ≤ U) (hWgH : Wg ≤ H) (hDW : D ≤ W) (hsource : ⁅Wg, W⁆ ≤ E) :
    second H T ∈ YFamily H T V₂ E :=
  second_mem_Y_of_tilde_plane hX hUT hn hVU hZV hZE (c.moved_tilde_card hVU)
    (c.moved_tilde_le_constituent_commutator hVU hDU hWgH) hDW hsource

/-- All commutator and order conclusions under the natural constituent marks,
using its source construction as [Ũ,x] and the earlier 12.8.11(1) bound. -/
theorem Coordinates.second_mem_Y_of_source [Finite G] [IsExtraspecial 2 U]
    (c : Coordinates H T U V₂ D Wg hn) {E W A : Subgroup G}
    (hX : second H T ∈ XFamily H T) (hUT : U ≤ T) (hVU : V₂ ≤ U)
    (hZV : center U ≤ V₂.subgroupOf U) (hZE : center U ≤ E.subgroupOf U)
    (hDU : D ≤ U) (hWgH : Wg ≤ H) (hEW : E ≤ W)
    (hD : tilde U D = tilde U ⁅U, A⁆) (hA : A ≤ Wg)
    (hindex : W.relIndex U = 2) (hsource : ⁅Wg, W⁆ ≤ E) :
    second H T ∈ YFamily H T V₂ E := by
  have hAW : A ≤ normalizer (W : Set G) := hA.trans
    (le_normalizer_iff_commutator_le_right.mpr (hsource.trans hEW))
  have hDW : D ≤ W := constituent_le_of_invariant_hyperplane hDU
    (hZE.trans (subgroupOf_mono U hEW)) hD hindex (hA.trans (hWgH.trans hn)) hAW
  exact c.second_mem_Y hX hUT hVU hZV hZE hDU hWgH hDW hsource

/-- The common family calculation and first-member result now yield X=Y.
Constructing the coordinate marks remains an obligation of the natural
geometry producer; the family hypotheses are the common branch's outputs. -/
theorem Coordinates.families_eq_of_source [Finite G] [IsExtraspecial 2 U]
    (c : Coordinates H T U V₂ D Wg hn) {E W A : Subgroup G}
    (hpair : XFamily H T = {first H, second H T})
    (hfirst : first H ∈ YFamily H T V₂ E)
    (hUT : U ≤ T) (hVU : V₂ ≤ U)
    (hZV : center U ≤ V₂.subgroupOf U) (hZE : center U ≤ E.subgroupOf U)
    (hDU : D ≤ U) (hWgH : Wg ≤ H) (hEW : E ≤ W)
    (hD : tilde U D = tilde U ⁅U, A⁆) (hA : A ≤ Wg)
    (hindex : W.relIndex U = 2) (hsource : ⁅Wg, W⁆ ≤ E) :
    XFamily H T = YFamily H T V₂ E := by
  have hX : second H T ∈ XFamily H T := by rw [hpair]; simp
  exact families_eq_of_second_mem_Y hpair hfirst
    (c.second_mem_Y_of_source hX hUT hVU hZV hZE hDU hWgH hEW hD hA hindex hsource)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural

module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Family
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Quotients
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.MarkedModule
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Geometry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Placements

/-!
# The natural-module branch of the tensor calculation

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 14.4.10,
printed pp.1010–1011, natural L₂(4)-module case.

The actual component Sylow and its Borel give the two placement identities
needed to construct natural coordinates on the selected constituent of U/Z(U).
The Borel cubic expands the binary point to its F₄-line, and a root in Wᵍ
places that line in the constituent commutator. The source hyperplane and
12.8.11(1) bound put the commutator in E. Extraspeciality then supplies the
central factor: the actual [V₂,X₂] has order eight, so X₂ belongs to Y and X=Y.

Only after this membership is established do we apply the earlier 14.4.8
implication. The marked C₂ × A₄ placement excludes the alternating actor,
forcing H/O₂(H) ≃ S₃ × S₅. Its marked S₃ × S₄ overlap gives the whole
X₁X₂T/O₂(X₁X₂T) ≃ S₃ × S₃, with the literal quotient-map formula retained.

`natural_branch_of_source` proves this branch from the unmarked natural
constituent, the common-family outputs, and the precise earlier-source inputs
listed in its statement. The parent Tensor assembly still owns those earlier
inputs, the common-family calculation and exclusion of the other constituent.
No coordinate marks, desired image equivalences or branch conclusions are
assumed by this theorem.
-/

public section

open Subgroup Theory.SpecificGroups.TensorThreeFive
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural
open Representation.SL2FourNatural
variable {G : Type*} [Group G] [Finite G] {H T : Subgroup G}

/-- The literal component Sylow has order four, and the second residual is
its relative normalizer. Both placement premises of the coordinate construction
follow from the source Sylow and actor models. -/
theorem geometry_placements_of_sylow
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (eK : star H (component H) ≃* SL)
    (hmodel : Nonempty (coreQuotient H ≃* S3 × Equiv.Perm (Fin 5)) ∨
      Nonempty (coreQuotient H ≃* S3 × alternatingGroup (Fin 5))) :
    Geometry.Placements H T := by
  obtain ⟨⟨P, hP⟩, hI, hB⟩ := Placements.star_sylow_marks S hS
  have hKcard : Nat.card (star H (component H)) = 60 := by
    rw [Nat.card_congr eK.toEquiv, Atlas.card_sl_two,
      Nat.card_eq_fintype_card, card_field]
    norm_num
  have : (star H (component H)).Normal := Geometry.component_star_normal
  obtain ⟨Q, hQ⟩ := P.exists_sylow_map_eq_inf_of_normal (star H (component H))
  have hBmodel : Nonempty (star H (borel H T) ≃* A4) := by
    rcases hmodel with hm | hm
    · obtain ⟨e⟩ := hm
      obtain ⟨i, hi⟩ := Placements.symmetric_borel_image S hS e
      exact ⟨(e.subgroupMap _).trans ((MulEquiv.subgroupCongr hi).trans
        ((Placements.botProdEquiv _).trans (Placements.evenPointEquiv i)))⟩
    · obtain ⟨e⟩ := hm
      obtain ⟨i, hi⟩ := Placements.alternating_borel_image S hS e
      exact ⟨(e.subgroupMap _).trans ((MulEquiv.subgroupCongr hi).trans
        ((Placements.botProdEquiv _).trans (Placements.alternatingPointEquiv i)))⟩
  refine ⟨?_, ?_⟩
  · rw [hI, ← hP, ← hQ, card_map_of_injective (star H (component H)).subtype_injective,
      Q.card_eq_multiplicity, hKcard]
    decide +kernel
  · obtain ⟨eB⟩ := hBmodel
    rw [Placements.star_second_eq_borel eB, hB, inf_subgroupOf_left]
    exact subgroupOf_normalizer_eq (hI.trans_le inf_le_right)

variable {U V₂ D Wg E W A : Subgroup G}
  [IsElementaryAbelian 2 (U ⧸ center U)]

/-- The conclusions of the natural branch, with its chosen coordinates and
the literal quotient maps. This is an output, never a source assumption. -/
structure BranchConclusion (H T U V₂ D Wg E W : Subgroup G)
    [IsElementaryAbelian 2 (U ⧸ center U)]
    (hn : H ≤ normalizer (U : Set G))
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T) where
  coordinates : Coordinates H T U V₂ D Wg hn
  field_point : ∃ L : Submodule F V, Module.finrank F L = 1 ∧
    Representation.BinaryOffender.binarySubgroup
      ((L.restrictScalars (ZMod 2)).map coordinates.embedding) =
        tilde U (movedSpace V₂ (second H T))
  point_le_moved : tilde U V₂ ≤ tilde U (movedSpace V₂ (second H T))
  moved_le_constituent : tilde U (movedSpace V₂ (second H T)) ≤ tilde U D
  constituent_le_hyperplane : D ≤ W
  moved_le_commutator : tilde U (movedSpace V₂ (second H T)) ≤ tilde U ⁅D, Wg⁆
  commutator_le_E : tilde U ⁅D, Wg⁆ ≤ tilde U E
  moved_card : Nat.card (movedSpace V₂ (second H T)) = 8
  moved_le_E : movedSpace V₂ (second H T) ≤ E
  second_mem_Y : second H T ∈ YFamily H T V₂ E
  families_eq : XFamily H T = YFamily H T V₂ E
  actor : coreQuotient H ≃* S3 × Equiv.Perm (Fin 5)
  quotient : coreQuotient (overlap H T) ≃* S3 × S3
  quotient_mk : ∀ x : overlap H T,
    quotient (QuotientGroup.mk' _ x) =
      overlapMap (Placements.symmetricPlacement S hS actor
        (starHom (overlap_le (hS ▸ map_subtype_le _)) x))

/-- The natural-module branch of 14.4.10, conditional only on the named
earlier-source and common-family inputs. The natural constituent is unmarked:
all point, root, Borel and Sylow coordinates are constructed here. The 14.4.8
implication is applied only after proving membership of the actual X₂ in Y.

The common-family owner supplies `hpair`, `hfirst`, `hVD`, and the construction
`hD` with `hA`. The source 14.4.2 action supplies `n`, `hmodel`, and `hWcard`;
the earlier 12.8/14.3/14.4.7 data supply the fixed point, extraspeciality,
central containments and hyperplane. `hsource` is exactly 12.8.11(1).
The parent retains discharge of these inputs from Hypothesis 14.3.10. -/
theorem natural_branch_of_source [IsExtraspecial 2 U]
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hn : H ≤ normalizer (U : Set G)) (n : Geometry.Constituent H U D hn)
    (hmodel : Nonempty (coreQuotient H ≃* S3 × Equiv.Perm (Fin 5)) ∨
      Nonempty (coreQuotient H ≃* S3 × alternatingGroup (Fin 5)))
    (hpoint : Nat.card (tilde U V₂) = 2) (hVD : tilde U V₂ ≤ tilde U D)
    (hfixed : ∀ h : H, (h : G) ∈ T ∨ (h : G) ∈ Wg →
      ∀ q ∈ tilde U V₂, Geometry.representation hn h (Additive.ofMul q) = Additive.ofMul q)
    (hWcard : Nat.card (star H Wg) = 8)
    (hpair : XFamily H T = {first H, second H T})
    (hfirst : first H ∈ YFamily H T V₂ E)
    (hUT : U ≤ T) (hVU : V₂ ≤ U)
    (hZV : center U ≤ V₂.subgroupOf U) (hZE : center U ≤ E.subgroupOf U)
    (hDU : D ≤ U) (hWgH : Wg ≤ H) (hEW : E ≤ W)
    (hD : tilde U D = tilde U ⁅U, A⁆) (hA : A ≤ Wg)
    (hindex : W.relIndex U = 2) (hsource : ⁅Wg, W⁆ ≤ E)
    (h148 : ∀ X ∈ YFamily H T V₂ E, Nonempty (coreQuotient (X ⊔ T) ≃* S3)) :
    Nonempty (BranchConclusion H T U V₂ D Wg E W hn S hS) := by
  obtain ⟨c⟩ := Geometry.exists_coordinates_of_model hn n
    (geometry_placements_of_sylow S hS n.componentEquiv hmodel)
    hmodel hpoint hVD hfixed hWcard
  have hX : second H T ∈ XFamily H T := by rw [hpair]; simp
  have hAW : A ≤ normalizer (W : Set G) := hA.trans
    (le_normalizer_iff_commutator_le_right.mpr (hsource.trans hEW))
  have hDW : D ≤ W := constituent_le_of_invariant_hyperplane hDU
    (hZE.trans (subgroupOf_mono U hEW)) hD hindex (hA.trans (hWgH.trans hn)) hAW
  have hY := c.second_mem_Y hX hUT hVU hZV hZE hDU hWgH hDW hsource
  obtain ⟨eH⟩ := Placements.symmetric_five_of_sylow S hS hmodel (h148 _ hY)
  obtain ⟨hfield, hpointMoved, hconstituent⟩ := c.moved_tilde_is_field_point hVU
  exact ⟨{
    coordinates := c
    field_point := hfield
    point_le_moved := hpointMoved
    moved_le_constituent := hconstituent
    constituent_le_hyperplane := hDW
    moved_le_commutator := c.moved_tilde_le_constituent_commutator hVU hDU hWgH
    commutator_le_E := constituent_commutator_tilde_le hDW hsource
    moved_card := hY.2.1
    moved_le_E := hY.2.2
    second_mem_Y := hY
    families_eq := families_eq_of_second_mem_Y hpair hfirst hY
    actor := eH
    quotient := Placements.overlapQuotient S hS eH
    quotient_mk := Placements.overlapQuotient_mk S hS eH }⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural

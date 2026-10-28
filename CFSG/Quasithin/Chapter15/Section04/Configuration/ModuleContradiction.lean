module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.PairwiseRecognition
public import Theory.GroupTheory.OrderFourIntersectionObstruction

/-!
# The final contradiction inside the source commutator module

For both X-factors, the module [V(M₁),Xᵢ] lies in the abelian group V(M₁)
because Xᵢ normalizes it. Genuine 15.4.22 recognition for the two pairs
(X₁,Y₁) and (X₂,Y₁) identifies these modules with the factor two-cores.
Their two nontrivial intersections with the order-four Y-module force that
module into V(M₁), contradicting the recognized dihedral join.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the paragraph
after 15.4.23, printed p.1165. The source uses O₂(X) as an abelian containing
subgroup; the already available V(M₁) suffices for this implication. This
does not assert the separate stronger equality O₂(X) = E₁₆. The actual
normal A₆ supplements and S₆ quotients remain earlier recognition inputs.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section04.Source

variable {G : Type*} [Group G] [Finite G] {d : Geometry G}

omit [Finite G] in
theorem LocalData.V₁_le_VM₁ (h : LocalData d) (i : Bool) : d.V₁ i ≤ d.VM₁ := by
  have hX : d.X i ≤ d.wholeX := by
    cases i
    · exact le_sup_left
    · exact le_sup_right
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((hX.trans d.wholeX.le_normalizer).trans h.VM₁_normalized)

theorem LocalData.false_of_pairwise_exceptional_recognition (h : LocalData d)
    (K : ∀ i : Bool, Subgroup (d.I i false)) [∀ i, (K i).Normal]
    (hgen : ∀ i, K i ⊔ (h.sylow i false : Subgroup (d.I i false)) = ⊤)
    (eK : ∀ i, K i ≃* alternatingGroup (Fin 6))
    [∀ i, (((d.T : Subgroup G) ⊓
      centralizer ((K i).map (d.I i false).subtype : Set G)).subgroupOf (d.I i false)).Normal]
    (eT : ∀ i, ((d.I i false) ⧸ (((d.T : Subgroup G) ⊓
      centralizer ((K i).map (d.I i false).subtype : Set G)).subgroupOf (d.I i false))) ≃*
        Equiv.Perm (Fin 6)) : False := by
  obtain ⟨_, _, ⟨e⟩, hAB⟩ :=
    h.pairwise_commutator_modules false false (K false) (hgen false) (eK false) (eT false)
  obtain ⟨_, _, _, hA'B⟩ :=
    h.pairwise_commutator_modules true false (K true) (hgen true) (eK true) (eT true)
  let _ := h.VM₁_elementary
  exact no_dihedral_join_of_order_four_intersections
    (h.V₁_le_VM₁ false) (h.V₁_le_VM₁ true) h.V₁_disjoint hAB hA'B (h.V₂_card false) e

end CFSG.Quasithin.Chapter15.Section04.Source

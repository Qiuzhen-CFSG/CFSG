module

public import Theory.SpecificGroups.Janko4.SmallBinaryAction
public import Theory.GroupAction.QuotientConjugation
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.Quotients

/-!
# Excluding the J₄ component by its action on the order-64 lift

Conjugation on the normal elementary subgroup D factors through the literal
quotient N/O₂(N), because O₂(N) centralizes D. A simple image isomorphic to
the actual J₄ carrier has trivial action on D: the certified local subgroup
makes 23 divide its order, whereas 23 cannot divide |GL₆(2)|.

The final adapter uses the parent development's exact `localSectionMap`
inside N_G(D). The existence of the containing component, its simple quotient
and model equivalence, and the smaller subgroup's nontrivial action remain
explicit premises. They belong to the source assembly, not to this obstruction.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.14(10),
printed pp.49–50, and the terminal component sieve in 14.4.9, printed p.1010.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.JankoFour

variable {N : Type*} [Group N] [Finite N]

/-- A simple J₄ image in the actual two-core quotient centralizes D.
Simplicity is inherited from the source component, not asserted for the model. -/
theorem quotient_image_centralizes
    (D K : Subgroup N) [D.Normal] [IsElementaryAbelian 2 D]
    (hD : Nat.card D = 64)
    (hcore : pCore 2 N ≤ centralizer (D : Set N))
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 N)))]
    (e : K.map (QuotientGroup.mk' (pCore 2 N)) ≃* Janko4.Model) :
    K ≤ centralizer (D : Set N) := by
  apply MulAut.le_centralizer_of_quotientConjNormal_image_eq_one D (pCore 2 N) K hcore
  exact Janko4.hom_mulAut_eq_one_of_card_eq_sixtyFour e hD _

/-- The literal nontrivial commutator required by the sieve contradicts
an actual simple J₄ quotient image of its containing subgroup. -/
theorem false_of_nontrivial_commutator
    (D K B : Subgroup N) [D.Normal] [IsElementaryAbelian 2 D]
    (hD : Nat.card D = 64)
    (hcore : pCore 2 N ≤ centralizer (D : Set N))
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 N)))]
    (e : K.map (QuotientGroup.mk' (pCore 2 N)) ≃* Janko4.Model)
    (hBK : B ≤ K) (hmoves : ⁅B, D⁆ ≠ ⊥) : False := by
  exact hmoves (commutator_eq_bot_iff_le_centralizer.mpr
    (hBK.trans (quotient_image_centralizes D K hD hcore e)))

variable {G : Type*} [Group G] [Finite G]

/-- The source normalizer formulation, with the exact range of
`localSectionMap` used by the component-sieve owner. -/
theorem normalizer_component_centralizes
    (D K : Subgroup G) [IsElementaryAbelian 2 D]
    (hD : Nat.card D = 64) (hKN : K ≤ normalizer (D : Set G))
    (hcore : (normalizer (D : Set G)).pCoreIn 2 ≤ centralizer (D : Set G))
    [IsSimpleGroup (localSectionMap (normalizer (D : Set G)) K hKN).range]
    (e : (localSectionMap (normalizer (D : Set G)) K hKN).range ≃* Janko4.Model) :
    K ≤ centralizer (D : Set G) := by
  let N := normalizer (D : Set G)
  let D' := D.subgroupOf N
  let K' := K.subgroupOf N
  let : D'.Normal := normal_subgroupOf_of_le_normalizer (le_refl N)
  let : IsElementaryAbelian 2 D' := IsElementaryAbelian.subgroupOf D.le_normalizer
  have hD' : Nat.card D' = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe D.le_normalizer).toEquiv).trans hD
  have hcore' : pCore 2 N ≤ centralizer (D' : Set N) := by
    intro n hn d hd
    apply Subtype.ext
    exact hcore (mem_map_of_mem N.subtype hn) d hd
  let c : K'.map (QuotientGroup.mk' (pCore 2 N)) ≃*
      (localSectionMap N K hKN).range :=
    MulEquiv.subgroupCongr (localSectionMap_range N K hKN).symm
  let : IsSimpleGroup (K'.map (QuotientGroup.mk' (pCore 2 N))) := c.isSimpleGroup
  have hc := quotient_image_centralizes D' K' hD' hcore' (c.trans e)
  intro k hk d hd
  have hh := hc (show (⟨k, hKN hk⟩ : N) ∈ K' from hk)
    (⟨d, D.le_normalizer hd⟩ : N) hd
  exact congrArg Subtype.val hh

/-- The J₄ branch is impossible once the parent constructs its containing
component and the nontrivial action of B on the actual lift D. -/
theorem false_of_normalizer_component
    (D K B : Subgroup G) [IsElementaryAbelian 2 D]
    (hD : Nat.card D = 64) (hKN : K ≤ normalizer (D : Set G))
    (hcore : (normalizer (D : Set G)).pCoreIn 2 ≤ centralizer (D : Set G))
    [IsSimpleGroup (localSectionMap (normalizer (D : Set G)) K hKN).range]
    (e : (localSectionMap (normalizer (D : Set G)) K hKN).range ≃* Janko4.Model)
    (hBK : B ≤ K) (hmoves : ⁅B, D⁆ ≠ ⊥) : False := by
  exact hmoves (commutator_eq_bot_iff_le_centralizer.mpr
    (hBK.trans (normalizer_component_centralizes D K hD hKN hcore e)))

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.JankoFour

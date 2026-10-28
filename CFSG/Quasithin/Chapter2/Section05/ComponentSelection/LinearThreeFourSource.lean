module

public import Theory.SpecificGroups.PSL3Three.FourNormalizer.FullNormalizer

/-!
# The PSL₃(3) four-subgroup clause of the original small-model source

For the PSL₃(3) alternative in 2.5.2(3), the actual relative normalizer
`K ∩ N_G(F)` is S₄ for every elementary four `F ≤ K`. Restricting to `K`
preserves the subgroup cardinality and elementary structure, and the actual
PSL model theorem then supplies the normalizer, centralizer, and full
pointwise automorphism-fixer calculations.

Source: Aschbacher--Smith, quasithin manuscript, 2.5.2(3), p.551, and
2.5.8(5), pp.556--557. The additional containment in the specified ambient
Sylow automorphism group remains with the source assembly.
-/

public section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup
variable {G : Type*} [Group G]

/-- The literal relative normalizer in the PSL₃(3) source alternative is S₄. -/
theorem linearThree_four_normalizer_source (K F : Subgroup G)
    (e : K ≃* Matrix.PSL3Three.PSL) (hFK : F ≤ K)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    Nonempty ((K ⊓ normalizer (F : Set G) : Subgroup G) ≃* Equiv.Perm (Fin 4)) := by
  let : IsElementaryAbelian 2 F := hF
  have hA : IsElementaryAbelian 2 (F.subgroupOf K) := IsElementaryAbelian.subgroupOf hFK
  have hcard : Nat.card (F.subgroupOf K) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFK).toEquiv).trans hc
  obtain ⟨f⟩ := Matrix.PSL3Three.normalizer_four_nonempty_equiv_of_equiv e
    (F.subgroupOf K) hA hcard
  let g : (K ⊓ normalizer (F : Set G) : Subgroup G) ≃*
      normalizer (F.subgroupOf K : Set K) :=
    (subgroupOfEquivOfLe (show K ⊓ normalizer (F : Set G) ≤ K from inf_le_left)).symm.trans
      (MulEquiv.subgroupCongr ((inf_subgroupOf_left _ _).trans
        (subgroupOf_normalizer_eq hFK)))
  exact ⟨g.trans f⟩

/-- The relative centralizer in the same actual source carrier is the four itself. -/
theorem linearThree_four_centralizer_source (K F : Subgroup G)
    (e : K ≃* Matrix.PSL3Three.PSL) (hFK : F ≤ K)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    K ⊓ centralizer (F : Set G) = F := by
  let : IsElementaryAbelian 2 F := hF
  have hh := Matrix.PSL3Three.centralizer_four_of_equiv e (F.subgroupOf K)
    (IsElementaryAbelian.subgroupOf hFK)
    ((Nat.card_congr (subgroupOfEquivOfLe hFK).toEquiv).trans hc)
  apply le_antisymm
  · intro x hx
    have hx' : (⟨x, hx.1⟩ : K) ∈ centralizer (F.subgroupOf K : Set K) := by
      intro y hy
      exact Subtype.ext (hx.2 y.val hy)
    rw [hh] at hx'
    exact hx'
  · exact le_inf hFK (Subgroup.le_centralizer F)

/-- The full automorphism fixer of the source four has order eight. -/
theorem linearThree_four_fixer_source (K F : Subgroup G)
    (e : K ≃* Matrix.PSL3Three.PSL) (hFK : F ≤ K)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    Nat.card (fixingSubgroup (MulAut K) (F.subgroupOf K : Set K)) = 8 := by
  let : IsElementaryAbelian 2 F := hF
  exact Matrix.PSL3Three.card_four_fixer_of_equiv e (F.subgroupOf K)
    (IsElementaryAbelian.subgroupOf hFK)
    ((Nat.card_congr (subgroupOfEquivOfLe hFK).toEquiv).trans hc)

/-- The full automorphism normalizer of the literal inner source four has order 48. -/
theorem linearThree_four_fullNormalizer_source (K F : Subgroup G)
    (e : K ≃* Matrix.PSL3Three.PSL) (hFK : F ≤ K)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    Nat.card (normalizer ((F.subgroupOf K).map (MulAut.conj : K →* MulAut K) :
      Set (MulAut K))) = 48 := by
  let : IsElementaryAbelian 2 F := hF
  exact Matrix.PSL3Three.card_four_fullNormalizer_of_equiv e (F.subgroupOf K)
    (IsElementaryAbelian.subgroupOf hFK)
    ((Nat.card_congr (subgroupOfEquivOfLe hFK).toEquiv).trans hc)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

module
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
/-!
# Normal subgroups inside a characteristic-two uniqueness subgroup

If J has characteristic two, every nontrivial subgroup normal in J has
nontrivial two-core. Its full ambient normalizer lies in the normalizer of
that characteristic two-core. If J has a unique maximal two-local
overgroup M, this forces the full normalizer into M.

This is the normalizer argument used in the covered case of
Aschbacher--Smith 13.2.2(9), printed p.878.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem normalizer_le_of_characteristic_two_unique
    {J M B : Subgroup G} (hJ : centralizer (pCore 2 J : Set J) ≤ pCore 2 J)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → J ≤ N → N = M)
    (hBJ : B ≤ J) (hne : B ≠ ⊥) (hn : J ≤ normalizer (B : Set G)) :
    normalizer (B : Set G) ≤ M := by
  let : (B.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hn
  have hc : centralizer (pCore 2 B : Set B) ≤ pCore 2 B :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hBJ)).mp
      (subnormal_core_selfCentralizing hJ _ (Normal.isSubnormal inferInstance))
  have hcore : pCore 2 B ≠ ⊥ := by
    intro he
    apply hne
    apply bot_unique
    intro b hb
    have hm : (⟨b, hb⟩ : B) ∈ pCore 2 B := by
      apply hc
      intro y hy
      have hy1 : y = 1 := mem_bot.mp (he ▸ hy)
      simp only [hy1, one_mul, mul_one]
    have hb1 : (⟨b, hb⟩ : B) = 1 := mem_bot.mp (he ▸ hm)
    exact congrArg (fun x : B => (x : G)) hb1
  have hNB := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  apply hNB.trans
  exact normalizer_le_of_unique_maximalTwoLocal hunique
    (pCore_isPGroup.map B.subtype)
    (fun he => hcore (((pCore 2 B).map_eq_bot_iff_of_injective B.subtype_injective).mp he))
    (hn.trans hNB)
end Theory.GroupTheory

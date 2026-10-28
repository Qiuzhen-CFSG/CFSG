module
public import Theory.GroupTheory.ElementaryThompsonComponent
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Thompson commutators above a quasisimple two-core quotient

A normal C-component K supplementing a Sylow two-subgroup S satisfies
K=[K,J(S)] if K/O₂(K) is quasisimple and K does not normalize J(S).
The radical-normalizer alternative would make N_K(J(S)) a supplement
to the solvable radical. The two-core normalizes that supplement since
it lies in S. Perfectness and the quasisimple quotient then force the
supplement to equal K, contradicting the normalizer hypothesis.

Source application: Aschbacher--Smith 14.2.15, printed p.986.
-/

public section
open Subgroup Theory.GroupTheory
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

theorem eq_commutator_maxJ_of_quasisimple_core_of_not_normalizes
    (S : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hgen : K ⊔ (S : Subgroup G) = ⊤)
    (hnot : ¬ K ≤ normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G)) :
    K = ⁅K,elementaryAbelianMaxJ (S : Subgroup G)⁆ := by
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let D := K ⊓ normalizer (J : Set G)
  have hSN : (S : Subgroup G) ≤ normalizer (J : Set G) :=
    (S : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  have hTS : K.pCoreIn 2 ≤ (S : Subgroup G) :=
    (pCoreIn_le_of_subnormal 2 hK.subnormal).trans (pCore_isPGroup.le_sylow_of_normal S)
  have hSD : (S : Subgroup G) ≤ normalizer (D : Set G) :=
    (le_inf le_normalizer_of_normal (hSN.trans (normalizer (J : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  apply eq_commutator_maxJ_of_radical_normalizer_lt S K hK hgen
  refine lt_of_le_not_ge (sup_le (map_subtype_le _) inf_le_left) ?_
  intro hle
  have he : (solvableRadical K).map K.subtype ⊔ D = K :=
    le_antisymm (sup_le (map_subtype_le _) inf_le_left) hle
  have hgenD : solvableRadical K ⊔ D.subgroupOf K = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show D ≤ K from inf_le_left),
      ←MonoidHom.range_eq_map,range_subtype]
    exact he
  have hQD : pCore 2 K ≤ normalizer (D.subgroupOf K : Set K) := by
    rw [←subgroupOf_normalizer_eq (show D ≤ K from inf_le_left)]
    intro x hx
    exact hSD (hTS (mem_map.mpr ⟨x,hx,rfl⟩))
  let := hK.perfect
  have hDtop := eq_top_of_radical_supplement_of_quasisimple_quotient
    (pCore 2 K) (D.subgroupOf K) hQD hgenD
  exact hnot ((subgroupOf_eq_top.mp hDtop).trans inf_le_right)
end Stellmacher

module
public import Theory.GroupTheory.Commutator.RelativeGeneration
/-!
# Derived subgroups with a central supplement modulo a layer

Suppose Q = JK, with K and Y normalized by Q, and [J,Q] contained in Y.
If Y is contained in Q', then Q' = Y K'. The proof expands commutators
through the two factors using only normality in Q. In particular it does
not infer that Q/Y is abelian without controlling K'.

Source application: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs*
(1985), the derived-core calculation preceding (12.9)(3), printed p.188.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]
/-- A supplement central modulo Y reduces the derived subgroup to Y and
that of the remaining factor; normality is relative to Q. -/
theorem commutator_eq_sup_of_central_modulo_supplement
    (Q J K Y : Subgroup G) (hgen : J ⊔ K = Q)
    (hQK : Q ≤ normalizer (K : Set G)) (hQY : Q ≤ normalizer (Y : Set G))
    (hcomm : ⁅J,Q⁆ ≤ Y) (hY : Y ≤ ⁅Q,Q⁆) :
    ⁅Q,Q⁆ = Y ⊔ ⁅K,K⁆ := by
  have hJQ : J ≤ Q := hgen ▸ le_sup_left
  have hKQ : K ≤ Q := hgen ▸ le_sup_right
  have hQder : Q ≤ normalizer ((⁅K,K⁆ : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hQK hg)]
  have hQT : Q ≤ normalizer ((Y ⊔ ⁅K,K⁆ : Subgroup G) : Set G) :=
    (le_inf hQY hQder).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_antisymm _ (sup_le hY (commutator_mono hKQ hKQ))
  have hK : ⁅K,Q⁆ ≤ Y ⊔ ⁅K,K⁆ := by
    rw [commutator_comm,←hgen]
    exact commutator_sup_le_of_relative_normal Q J K K (Y ⊔ ⁅K,K⁆) hQT hJQ hKQ
      (((commutator_mono le_rfl hKQ).trans hcomm).trans le_sup_left) le_sup_right
  conv_lhs => rw [←hgen]
  apply commutator_sup_le_of_relative_normal Q J K (J ⊔ K) (Y ⊔ ⁅K,K⁆) hQT hJQ hKQ
  · rw [hgen]
    exact hcomm.trans le_sup_left
  · rwa [hgen]
end Subgroup

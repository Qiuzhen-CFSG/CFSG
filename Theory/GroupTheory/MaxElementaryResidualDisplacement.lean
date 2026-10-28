module
public import Stellmacher.ElementaryAbelianMaxSylowImages
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Maximum elementary actors and the two-residual

Suppose a Sylow two-subgroup normalizes V and all its maximum elementary
subgroups centralize V. Every maximum elementary actor then has its
commutator with the full orbit span of V in O²(G). Modulo O²(G), the Sylow
subgroup surjects and V becomes normal; matching the actor's quotient image
with an actor in that Sylow subgroup proves the assertion.

This supplies the residual-containment step for the literal commutator plane
in Aschbacher--Smith 15.2.11, printed p.1111.
-/

public section
open Subgroup Stellmacher
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- All maximum elementary actors displace the orbit span into the two-residual. -/
theorem maxElementary_span_commutator_le_pResidual
    (S : Sylow 2 G) (V A : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (V : Set G))
    (hc : ∀ D ∈ elementaryAbelianMaxSubgroups (S : Subgroup G),
      D ≤ centralizer (V : Set G))
    (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G)) :
    ⁅conjugateSpanBy V ⊤,A⁆ ≤ pResidual 2 G := by
  let K := pResidual 2 G
  let q := QuotientGroup.mk' K
  have hSq : (S : Subgroup G).map q = ⊤ := by
    have hm := congrArg (Subgroup.map q) (pResidual_sup_sylow_eq_top S)
    change (K ⊔ (S : Subgroup G)).map (QuotientGroup.mk' K) =
      (⊤ : Subgroup G).map (QuotientGroup.mk' K) at hm
    simpa only [Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective K)] using hm
  obtain ⟨D,hD,hDA⟩ := exists_maxFamily_sylow_same_image S q A hA (by rw [hSq]; exact le_top)
  have hVn : (⊤ : Subgroup (G ⧸ K)) ≤ normalizer (V.map q : Set (G ⧸ K)) := by
    rw [←hSq]
    exact (map_mono hn).trans (le_normalizer_map q)
  have hU : (conjugateSpanBy V ⊤).map q = V.map q := by
    rw [map_conjugateSpanBy,map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
    exact le_antisymm (conjugateSpanBy_le le_rfl hVn) (le_conjugateSpanBy _ _)
  have hVA : ⁅V.map q,A.map q⁆ = ⊥ := by
    rw [←hDA,←map_commutator,
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp (hc D hD)),map_bot]
  have hm : (⁅conjugateSpanBy V ⊤,A⁆).map q = ⊥ := by
    rw [map_commutator,hU,hVA]
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm

end Subgroup

module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PrimeRankProduct

/-!
# Normality of centerless components of large prime rank

Distinct component conjugates commute. If a component is centerless, their
intersection is trivial, so their prime ranks add. Thus a centerless
component of p-rank at least two is normal whenever the ambient p-rank
is at most two.

Source application: the PSL3(3) and M11 alternatives in Aschbacher--Smith
2.5.3(4), printed p.553. The source group's nontrivial two-core supplies
its ordinary odd-prime-rank bound from ambient quasithinness.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A centerless rank-two component cannot have a distinct conjugate in
a group whose rank at that prime is at most two. -/
theorem IsComponent.normal_of_centerless_primeRank
    {D : Subgroup G} (hD : IsComponent G D) (hc : center D = ⊥)
    (hD2 : 2 ≤ primeRank p D) (hG2 : primeRank p G ≤ 2) : D.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  let E := D.map (MulAut.conj g).toMonoidHom
  have hDE : D ≤ centralizer (E : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (hD.commutator_eq_bot_of_ne (hD.map_conj g) (fun he => hne he.symm))
  have hd : Disjoint D E := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hxD, hxE⟩
    have hz : (⟨x, hxD⟩ : D) ∈ center D := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext ((le_centralizer_iff.mp hDE) hxE y y.property)
    have h1 : (⟨x, hxD⟩ : D) = 1 := by simpa only [hc, mem_bot] using hz
    exact congrArg Subtype.val h1
  have he : primeRank p D = primeRank p E :=
    primeRank_equiv p ((MulAut.conj g).subgroupMap D)
  have hl := primeRank_le_of_injective p (D ⊔ E : Subgroup G).subtype Subtype.val_injective
  rw [primeRank_sup_eq_add_of_disjoint_commuting D E hd hDE p] at hl
  omega

end Theory.GroupTheory

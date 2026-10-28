module
public import Theory.GroupTheory.IrreducibleNormalizerCore

/-!
# The p-core on an irreducible p-section

Pass to the quotient by the lower normal subgroup. The section becomes a
minimal normal p-subgroup, centralized by the quotient p-core. Pulling back
commutators gives the original lower subgroup. The F.8 critical edge is an
application with p=2 and section V/V₁.
-/
@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The p-core acts trivially on a normal irreducible p-section. -/
theorem commutator_pCore_le_of_irreducible_section
    (N V : Subgroup G) [N.Normal] [V.Normal] (hNV : N ≤ V)
    (hp : IsPGroup p V)
    (hirr : ∀ E : Subgroup G, N ≤ E → E ≤ V → E.Normal → E = N ∨ E = V) :
    ⁅V, pCore p G⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let W := V.map q
  let : W.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  have hminimal (E : Subgroup (G ⧸ N)) (hE : E ≤ W) (hn : E.Normal) :
      E = ⊥ ∨ E = W := by
    let := hn
    have hpre : E.comap q ≤ V := by
      have hh := comap_mono (f := q) hE
      rwa [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNV] at hh
    have hnpre : N ≤ E.comap q := by
      intro x hx
      change q x ∈ E
      have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [hqx]
      exact E.one_mem
    have heq : (E.comap q).map q = E := map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N) _
    rcases hirr (E.comap q) hnpre hpre inferInstance with he | he
    · left
      rw [← heq, he]
      exact (map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
    · right
      rw [← heq, he]
  have hc := pCore_le_centralizer_of_minimal_normal_pSubgroup W (hp.map q) hminimal
  have hcore : (pCore p G).map q ≤ pCore p (G ⧸ N) :=
    le_sSup ⟨Normal.map inferInstance q (QuotientGroup.mk'_surjective N),
      pCore_isPGroup.map q⟩
  apply commutator_le.mpr
  intro v hv x hx
  apply (QuotientGroup.eq_one_iff _).mp
  change q ⁅v, x⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hc (hcore (mem_map_of_mem q hx)) (q v) (mem_map_of_mem q hv)

end Subgroup

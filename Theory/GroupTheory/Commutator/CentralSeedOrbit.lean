module
public import Theory.GroupTheory.Commutator.ConjugateSpan
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Enlarging a component seed orbit inside an involution centralizer

If the K-orbit of Z splits as U times a central cyclic subgroup, and
U=[U,K], then enlarging the orbit to H replaces U by its H-conjugate
span. The same span is exactly [⟨Z^H⟩,K] and is fully moved by K.
All normality is relative to H; the original cyclic subgroup is retained.
Source: Aschbacher--Smith 13.4.10(7), printed p.909.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- The larger moved orbit is the literal H-span of the original moved
module. No irreducibility or equality of the two moved modules is assumed. -/
theorem central_seed_overgroup_orbit
    (Z K H U : Subgroup G) (z : G)
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (hHz : H ≤ centralizer ({z} : Set G))
    (hzZ : z ∈ Z) (hZH : Z ≤ H)
    (hsplit : conjugateSpanBy Z K = U ⊔ zpowers z)
    (hmove : ⁅U,K⁆ = U) :
    let W := conjugateSpanBy Z H
    let Q := conjugateSpanBy U H
    W = Q ⊔ zpowers z ∧ ⁅W,K⁆ = Q ∧ ⁅Q,K⁆ = Q ∧
      H ≤ normalizer (Q : Set G) ∧ U ≤ Q ∧ Q ≤ W ∧
      H ⊓ centralizer (W : Set G) = H ⊓ centralizer (Q : Set G) := by
  let W := conjugateSpanBy Z H
  let Q := conjugateSpanBy U H
  have hU : U ≤ conjugateSpanBy Z K := hsplit.symm ▸ le_sup_left
  have hUW : U ≤ W := hU.trans (conjugateSpanBy_mono le_rfl hKH)
  have hQW : Q ≤ W := conjugateSpanBy_le hUW (le_normalizer_conjugateSpanBy Z H)
  have hHQ : H ≤ normalizer (Q : Set G) := le_normalizer_conjugateSpanBy U H
  have hHc : H ≤ centralizer (zpowers z : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using hHz
  have hW : W = Q ⊔ zpowers z := by
    apply le_antisymm
    · apply conjugateSpanBy_le ?_
        ((le_inf hHQ (hHc.trans (centralizer_le_normalizer _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _))
      apply (le_conjugateSpanBy Z K).trans
      rw [hsplit]
      exact sup_le_sup_right (le_conjugateSpanBy U H) _
    · exact sup_le hQW (zpowers_le.mpr (le_conjugateSpanBy Z H hzZ))
  have hQmove : ⁅Q,K⁆ = Q :=
    (conjugateSpanBy_eq_commutator_of_seed U H K K hKH hHK le_rfl hmove.symm).symm
  have hWK : ⁅W,K⁆ = Q := by
    apply le_antisymm
    · rw [hW]
      apply commutator_sup_le_of_relative_normal H Q (zpowers z) K Q hHQ
        (hQW.trans (conjugateSpanBy_le_self hZH))
        (zpowers_le.mpr (hZH hzZ)) hQmove.le
      exact (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (hKH.trans hHc))).le.trans bot_le
    · rw [←hQmove]
      exact commutator_mono hQW le_rfl
  refine ⟨hW,hWK,hQmove,hHQ,le_conjugateSpanBy U H,hQW,?_⟩
  apply le_antisymm (inf_le_inf_left H (centralizer_le hQW))
  intro x hx
  refine ⟨hx.1,?_⟩
  have hc : Q ⊔ zpowers z ≤ centralizer ({x} : Set G) :=
    sup_le (fun v hv => mem_centralizer_singleton_iff.mpr (hx.2 v hv))
      (fun v hv => mem_centralizer_singleton_iff.mpr (hHc hx.1 v hv))
  exact fun v hv => mem_centralizer_singleton_iff.mp (hc (hW ▸ hv))

end Subgroup

module
public import Theory.SpecificGroups.Alternating.FiveElementaryActors
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Two-core quotient rank from an alternating-five residual

The original two-residual and a Sylow two-subgroup generate H. Since the
residual modulo its own two-core is centerless, conjugation identifies
H/O₂(H) with a subgroup of its automorphism group. Transport through the
actual A₅ isomorphism and the proved Aut(A₅) two-rank bound finishes the
argument. The two residual and core operations remain distinct throughout.

Source: Aschbacher--Smith, 12.2.7(2) and the nonsolvable rank argument
in 12.2.18, printed pp.797 and 801. This is the rank consequence conditional
on the residual identification; it does not assert that identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace Theory.SpecificGroups.Alternating.FiveExtensionAction
variable {H : Type*} [Group H] [Finite H]

theorem twoCoreQuotient_rank_le_two_of_residual_five
    (e : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* alternatingGroup (Fin 5)) :
    primeRank 2 (H ⧸ pCore 2 H) ≤ 2 := by
  let K := pResidual 2 H
  let T : Sylow 2 H := Classical.choice inferInstance
  have hn : (T : Subgroup H) ≤ normalizer (K : Set H) := le_normalizer_of_normal
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply e.injective
    rw [map_one]
    apply mem_bot.mp
    rw [← alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5))]
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
  let E := pCoreJoinQuotientEquivRange 2 hn T.isPGroup' hz
  have hr : primeRank 2 ((K ⊔ (T : Subgroup H) : Subgroup H) ⧸
      pCore 2 (K ⊔ (T : Subgroup H) : Subgroup H)) ≤ 2 := by
    rw [primeRank_equiv 2 E]
    apply (Theory.GroupTheory.primeRank_le_of_injective 2
      (pCoreJoinAction 2 hn).range.subtype (pCoreJoinAction 2 hn).range.subtype_injective).trans
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact automorphism_primeRank_two_le
  have htop : K ⊔ (T : Subgroup H) = ⊤ := pResidual_sup_sylow_eq_top T
  rw [htop] at hr
  let q : ((⊤ : Subgroup H) ⧸ pCore 2 (⊤ : Subgroup H)) ≃* (H ⧸ pCore 2 H) :=
    QuotientGroup.congr _ _ topEquiv (pCore_map_iso 2 topEquiv)
  exact (primeRank_equiv 2 q).symm.le.trans hr

end Theory.SpecificGroups.Alternating.FiveExtensionAction

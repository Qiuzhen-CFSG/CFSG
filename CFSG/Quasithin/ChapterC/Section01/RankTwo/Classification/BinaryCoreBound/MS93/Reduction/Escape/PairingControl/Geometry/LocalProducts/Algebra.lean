module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Source
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Algebra for the local moving products

A commutator bound normalizes a join when its bounding subgroup is normalized.
In a finite group with the actual simple SL3(2) quotient and two-group kernel,
a subgroup outside that kernel normally generates a group containing the
two-residual. Thus a bound for its commutator with a normal two-group W
extends to the residual. Residual commutator idempotence strengthens the
bound from V to [V,O^2(G)].

These calculations are applied inside the finite vertex stabilizer, never
inside a purported finite free amalgam.
Source: MS93 (1993), the local-product paragraph of (4.3.2), printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts

theorem normalizes_sup_of_commutator_le {G : Type*} [Group G]
    (A B K : Subgroup G) (hKA : K ≤ normalizer (A : Set G))
    (hc : ⁅B, K⁆ ≤ A) : K ≤ normalizer (A ⊔ B : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have hm : (A ⊔ B).map (MulAut.conj k).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    apply sup_le
    · exact (mem_normalizer_iff_map_conj_eq.mp (hKA hk)).le.trans le_sup_left
    · rintro _ ⟨b, hb, rfl⟩
      have hcb : ⁅k, b⁆ ∈ A := by
        rw [commutator_comm] at hc
        exact hc (commutator_mem_commutator hk hb)
      have h := (A ⊔ B).mul_mem (mem_sup_left hcb) (mem_sup_right hb)
      simpa [commutatorElement_def, mul_assoc] using h
  exact hm (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)

theorem residual_commutator_bound {G : Type*} [Group G] [Finite G]
    (π : G →* SL) (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (W V J : Subgroup G) [W.Normal] [V.Normal] (hW : IsPGroup 2 W)
    (hJ : ¬ J ≤ π.ker) (hc : ⁅W, J⁆ ≤ V) :
    ⁅W, pResidual 2 G⁆ ≤ ⁅V, pResidual 2 G⁆ := by
  let N := normalClosure (J : Set G)
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hn : (N.map π).Normal := (inferInstance : N.Normal).map π hπ
  have htop : N.map π = ⊤ := by
    rcases hn.eq_bot_or_eq_top with h | h
    · exact False.elim (hJ (le_normalClosure.trans ((map_eq_bot_iff N).mp h)))
    · exact h
  have hgen : N ⊔ π.ker = ⊤ := by
    rw [← comap_map_eq, htop, comap_top]
  have hres : pResidual 2 G ≤ N :=
    sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N π.ker hker hgen⟩
  have hbound : ⁅W, pResidual 2 G⁆ ≤ V :=
    (commutator_mono le_rfl hres).trans (commutator_normalClosure_le_of_normal W J V hc)
  exact (commutator_isPPerfect_idempotent (pResidual 2 G) W
    (isPPerfect_pResidual 2) hW le_normalizer_of_normal).symm.le.trans
    (commutator_mono hbound le_rfl)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts

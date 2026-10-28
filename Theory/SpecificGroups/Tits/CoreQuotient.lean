module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.Source
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupTheory.CenterlessCentralizer
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The marked Tits subgroup modulo the entire ambient two-core

A normal subgroup with Tits central carrier has trivial center after its
own two-core is removed, by the complete universal-cover calculation.
The literal quotient map then identifies its image modulo the ambient
two-core with that same Tits carrier. A two-group supplement forces the
centralizer of this image to be trivial.

Source application: Aschbacher--Smith6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace Tits
variable {J : Type*} [Group J] [Finite J]

/-- The actual normal image retains the supplied marking and is
self-centralizing after quotienting by the entire ambient two-core. -/
theorem marked_core_quotient
    (B : Subgroup J) [B.Normal] [IsQuasisimple (B ⧸ pCore 2 B)]
    (hJB : IsPGroup 2 (J ⧸ B)) (e : coreCentralQuotient B ≃* ParrottGroup) :
    let q := QuotientGroup.mk' (pCore 2 J)
    let N := B.map q
    ∃ f : N ≃* ParrottGroup,
      (∀ b : B, f (q.subgroupMap B b) = e (coreCentralProjection B b)) ∧
      centralizer (N : Set (J ⧸ pCore 2 J)) = ⊥ := by
  let Q := J ⧸ pCore 2 J
  let q := QuotientGroup.mk' (pCore 2 J)
  let N := B.map q
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : N.Normal := (inferInstance : B.Normal).map q hq
  let eB : (B ⧸ pCore 2 B) ≃* ParrottGroup :=
    centralQuotientEquivOfUniversalKernelEqBot
      CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot e
  let f : N ≃* ParrottGroup := (coreQuotientEquivImage 2 B).symm.trans eB
  refine ⟨f,?_,?_⟩
  · intro b
    change eB ((coreQuotientEquivImage 2 B).symm (q.subgroupMap B b)) = _
    have he : (coreQuotientEquivImage 2 B) (QuotientGroup.mk' (pCore 2 B) b) =
        q.subgroupMap B b := Subtype.ext (coreQuotientEquivImage_apply_mk 2 B b)
    rw [←he,MulEquiv.symm_apply_apply]
    exact centralQuotientEquivOfUniversalKernelEqBot_apply _ e _
  · have hzB : center (B ⧸ pCore 2 B) = ⊥ :=
      center_eq_bot_of_centralQuotientEquiv
        CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot e
    have hzN : center N = ⊥ := by
      apply bot_unique
      intro x hx
      let j := (coreQuotientEquivImage 2 B).symm
      have he := (centerCongr j ⟨x,hx⟩).property
      change j x ∈ center (B ⧸ pCore 2 B) at he
      rw [hzB,mem_bot] at he
      exact j.injective (he.trans j.map_one.symm)
    obtain ⟨m,hm⟩ := hJB.exists_card_eq
    have hidx : N.index ∣ 2^m := (B.index_map_dvd hq).trans (by
      change Nat.card (J ⧸ B) ∣ 2^m
      rw [hm])
    have hCtwo : IsPGroup 2 (centralizer (N : Set Q)) :=
      IsPGroup.of_card_dvd_pow ((centralizer_card_dvd_index_of_center_eq_bot N hzN).trans hidx)
    have hle : centralizer (N : Set Q) ≤ pCore 2 Q := le_sSup ⟨inferInstance,hCtwo⟩
    exact bot_unique (hle.trans_eq (pCore_quotient_pCore_eq_bot 2))

end Tits

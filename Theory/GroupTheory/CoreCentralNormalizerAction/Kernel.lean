module
public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupAction.PerfectCentralQuotient
/-!
# Trivial central-core action detects the component core

An automorphism of a perfect group is detected on its central quotient.
Consequently a subgroup whose literal normalizer image on (K/O₂(K))/Z is
trivial has commutator with K contained in O₂(K). This preserves the actual
subgroup maps needed to turn source C.4.3 into a nontrivial action statement.

Source: Aschbacher--Smith C.4.3--5, printed p.152.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem commutator_le_core_of_coreCentralActorImage_eq_bot
    (K A : Subgroup G) [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hAK : A ≤ normalizer (K : Set G))
    (hb : coreCentralActorImage K A = ⊥) : ⁅A,K⁆ ≤ K.pCoreIn 2 := by
  apply commutator_le.mpr
  intro a ha k hk
  let a' : normalizer (K : Set G) := ⟨a,hAK ha⟩
  let k' : K := ⟨k,hk⟩
  let f := quotientAut (pCore 2 K) (K.normalizerMonoidHom a')
  have hc : quotientAut (center (K ⧸ pCore 2 K)) f = 1 :=
    hb.le (mem_map_of_mem (normalizerCoreCentralAction K) ha)
  have hf : f = 1 := MulAut.quotient_center_injective
    (hc.trans (map_one (quotientAut (center (K ⧸ pCore 2 K)))).symm)
  have he : QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom a' k') =
      QuotientGroup.mk' (pCore 2 K) k' := by
    have ht := congrArg (fun t : MulAut (K ⧸ pCore 2 K) =>
      t (QuotientGroup.mk' (pCore 2 K) k')) hf
    simpa only [f,quotientAut_apply_mk,MulAut.one_apply] using ht
  have hm : K.normalizerMonoidHom a' k' / k' ∈ pCore 2 K :=
    QuotientGroup.eq_iff_div_mem.mp he
  refine ⟨K.normalizerMonoidHom a' k' / k',hm,?_⟩
  change (a * k * a⁻¹) / k = ⁅a,k⁆
  simp only [div_eq_mul_inv,commutatorElement_def]
end Subgroup

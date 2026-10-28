module
public import Theory.GroupTheory.SplitExtensionCoordinates.Marked

/-!
# A marked split model from an actual normalizer action

An ambient elementary factor and its literal conjugation action determine
a split extension once their centralizer is the action kernel. This bridge
uses the same action-image equivalence and kernel coordinates, and records
the value on each original factor element as well as its canonical image.

The consumer is the natural split A₆ model in Aschbacher–Smith 14.3.19(9).
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G L W : Type*} [Group G] [Group L] [Group W]

theorem exists_marked_semidirect_equiv_of_normalizer_action
    (A K : Subgroup G) (hAK:A≤K) (hKA:K≤normalizer (A:Set G))
    (hker:K⊓centralizer (A:Set G)=A)
    (eA:(A.normalizerMonoidHom.comp (inclusion hKA)).range ≃* L)
    (eQ:A≃*W) (ρ:L→*MulAut W)
    (he:∀ (a:(A.normalizerMonoidHom.comp (inclusion hKA)).range) (v:A),
      eQ (a.val v)=ρ (eA a) (eQ v))
    (hsplit:∃ C:Subgroup K,(A.subgroupOf K).IsComplement' C) :
    ∃ e:K≃*W⋊[ρ]L,
      (∀u:A,e (inclusion hAK u)=SemidirectProduct.inl (eQ u)) ∧
      (A.subgroupOf K).map e.toMonoidHom=(SemidirectProduct.inl:W→*W⋊[ρ]L).range := by
  let AA:=A.subgroupOf K
  let : AA.Normal := (normal_subgroupOf_iff_le_normalizer hAK).mpr hKA
  let φ:=A.normalizerMonoidHom.comp (inclusion hKA)
  let f:K→*L:=eA.toMonoidHom.comp φ.rangeRestrict
  have hf:Function.Surjective f:=eA.surjective.comp φ.rangeRestrict_surjective
  have hk:f.ker=AA := by
    change (eA.toMonoidHom.comp φ.rangeRestrict).ker=AA
    rw [MonoidHom.ker_comp_of_injective _ _ eA.injective,MonoidHom.ker_rangeRestrict]
    ext x
    change inclusion hKA x∈A.normalizerMonoidHom.ker ↔ (x:G)∈A
    rw [normalizerMonoidHom_ker]
    change (x:G)∈centralizer (A:Set G) ↔ (x:G)∈A
    conv_rhs=>rw [←hker]
    simp only [mem_inf,x.property,true_and]
  let eqt:(K⧸AA)≃*L := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have heqt (k:K):eqt (QuotientGroup.mk' AA k)=f k := rfl
  let eqn:AA≃*W := (subgroupOfEquivOfLe hAK).trans eQ
  have heq (k:K) (a:AA):eqn (MulAut.conjNormal k a)=ρ (eqt (QuotientGroup.mk' AA k)) (eqn a) := by
    rw [heqt]
    exact he (φ.rangeRestrict k) ((subgroupOfEquivOfLe hAK) a)
  obtain ⟨C,hC⟩:=hsplit
  obtain ⟨e,heu,hem⟩:=exists_marked_semidirect_equiv_of_split_coordinates AA C hC eqt eqn ρ heq
  refine ⟨e,?_,hem⟩
  intro u
  exact heu ((subgroupOfEquivOfLe hAK).symm u)
end Subgroup

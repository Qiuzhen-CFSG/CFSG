module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuFrame
public import Theory.SpecificGroups.ReeTwo.CoreFiveActionNormalization

/-!
# Normalizing the original first-core five action

The actual B₅ action on Q₀Q₅ is faithful: otherwise the order-1024 core
would lie in its order-eight fixed subgroup. The checked Ree-core census
then conjugates a generator to the native five action while preserving
the fixed cyclic-four root and its central square. The final theorem
applies this normalization to the original TypeRu source frame.

Source: Aschbacher–Smith J.4.5, printed pp.441–442, and the verified
Shinoda core action used in the F.1.12 binary Ree branch.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

def firstCoreAction (B5:Sylow 5 d.toTypeRuSetup.H) (e:fiveHyperplane d B5≃*ReeTwo.Core) :
    normalizer (fiveHyperplane d B5:Set G)→*MulAut ReeTwo.Core :=
  (MulAut.congr e).toMonoidHom.comp (fiveHyperplane d B5).normalizerMonoidHom

theorem firstCoreAction_apply (B5:Sylow 5 d.toTypeRuSetup.H)
    (e:fiveHyperplane d B5≃*ReeTwo.Core) (b:normalizer (fiveHyperplane d B5:Set G))
    (q:fiveHyperplane d B5) :
    (e.symm (firstCoreAction B5 e b (e q)):G)=(b:G)*(q:G)*(b:G)⁻¹ := by
  change (e.symm (e ((fiveHyperplane d B5).normalizerMonoidHom b (e.symm (e q)))):G)=_
  rw [e.symm_apply_apply,e.symm_apply_apply]
  rfl

/-- Normalize the literal five action, while fixing the prescribed root and
its central square. -/
theorem normalized_firstCore_five_action (B5:Sylow 5 d.toTypeRuSetup.H)
    (t z:fiveHyperplane d B5) (ht:(t:G)∈centralizer (B5Image B5:Set G))
    (eQ:fiveHyperplane d B5≃*ReeTwo.Core)
    (het:eQ t=ReeTwo.Core.root 2) (hez:eQ z=ReeTwo.Core.root 9) :
    ∃(e:fiveHyperplane d B5≃*ReeTwo.Core)(c:B5Image B5),
      e t=ReeTwo.Core.root 2 ∧ e z=ReeTwo.Core.root 9 ∧
      zpowers (c:G)=B5Image B5 ∧ orderOf c=5 ∧
      ∀x:ReeTwo.Core,(e.symm (ReeTwo.Core.c x):G)=(c:G)*(e.symm x:G)*(c:G)⁻¹ := by
  let A:=B5Image B5
  let K:=fiveHyperplane d B5
  have hA:Nat.card A=5:=B5Image_card d.card_Z B5
  let : Fact (Nat.Prime 5):=⟨by decide⟩
  let : IsCyclic A:=isCyclic_of_prime_card hA
  obtain ⟨c,hc⟩:=IsCyclic.exists_generator (α:=A)
  have hAN:A≤normalizer (K:Set G):=(le_inf
    ((show A≤d.toTypeRuSetup.H from map_subtype_le _).trans (Q₀_normalized d))
    (normalizer_commutator_ge_right _ _)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let f: A→*MulAut ReeTwo.Core:=(firstCoreAction B5 eQ).comp (inclusion hAN)
  let rho:=f c
  have hrho:orderOf rho=5:=by
    apply orderOf_eq_prime
    · change f c^5=1
      rw [←map_pow,show c^5=1 from hA ▸ pow_card_eq_one' (x:=c),map_one]
    · intro he
      have htriv:∀b:A,f b=1:=by
        intro b
        obtain ⟨n,hn⟩:=mem_zpowers_iff.mp (hc b)
        rw [←hn,map_zpow]
        change rho^n=1
        rw [he,one_zpow]
      have hcentral:K≤centralizer (A:Set G):=by
        intro q hq b hb
        have hh:=firstCoreAction_apply B5 eQ (inclusion hAN ⟨b,hb⟩) ⟨q,hq⟩
        change (eQ.symm (f ⟨b,hb⟩ (eQ ⟨q,hq⟩)):G)=b*q*b⁻¹ at hh
        rw [htriv,MulAut.one_apply,eQ.symm_apply_apply] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh.symm
      have hKC:K≤CQ B5:=le_inf (fiveHyperplane_le_Q d B5) hcentral
      have hh:=card_le_of_le hKC
      rw [fiveHyperplane_card,five_centralizer_card] at hh
      omega
  have hroot:rho (ReeTwo.Core.root 2)=ReeTwo.Core.root 2:=by
    rw [←het]
    apply eQ.symm.injective
    apply Subtype.ext
    change (eQ.symm (firstCoreAction B5 eQ (inclusion hAN c) (eQ t)):G)=_
    rw [firstCoreAction_apply,eQ.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (ht c c.property)
  obtain ⟨delta,hdt,hdz,hd⟩:=ReeTwo.Core.exists_marked_conjugator_of_orderOf_eq_five rho hrho hroot
  let e:=eQ.trans delta
  have heaction:firstCoreAction B5 e (inclusion hAN c)=ReeTwo.Core.c:=by
    change delta*rho*delta⁻¹=ReeTwo.Core.c
    exact hd
  have hzpow:zpowers (c:G)=A:=by
    apply eq_of_le_of_card_ge (zpowers_le.mpr c.property)
    have ho:orderOf c=5:=(orderOf_eq_card_of_forall_mem_zpowers hc).trans hA
    rw [Nat.card_zpowers,orderOf_coe,ho,hA]
  have hco:orderOf c=5:=(orderOf_eq_card_of_forall_mem_zpowers hc).trans hA
  refine ⟨e,c,(congrArg delta het).trans hdt,(congrArg delta hez).trans hdz,hzpow,hco,?_⟩
  intro x
  have hh:=firstCoreAction_apply B5 e (inclusion hAN c) (e.symm x)
  rw [e.apply_symm_apply,heaction] at hh
  exact hh

/-- A marking of the actual first core and a literal generator of B₅ identify
its native action with the specified five-action on the Ree model. -/
theorem SourceChoice.exists_firstCore_five_marking (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃(e:fiveHyperplane d B5≃*ReeTwo.Core)(c:B5Image B5),
      zpowers (e.symm (ReeTwo.Core.root 9):G)=d.toTypeRuSetup.Z ∧
      (e.symm (ReeTwo.Core.root 2):G)∈centralizer (B5Image B5:Set G) ∧
      zpowers (c:G)=B5Image B5 ∧ orderOf c=5 ∧
      ∀x:ReeTwo.Core,(e.symm (ReeTwo.Core.c x):G)=(c:G)*(e.symm x:G)*(c:G)⁻¹ := by
  obtain ⟨e,hz,ht⟩:=s.exists_firstCore_marking B5 hi
  let t:=e (ReeTwo.Core.root 2)
  let z:=e (ReeTwo.Core.root 9)
  obtain ⟨e',c,het,hez,hc,hco,ha⟩:=normalized_firstCore_five_action B5 t z ht e.symm
    (e.symm_apply_apply _) (e.symm_apply_apply _)
  have het':e'.symm (ReeTwo.Core.root 2)=t:=by rw [←het,e'.symm_apply_apply]
  have hez':e'.symm (ReeTwo.Core.root 9)=z:=by rw [←hez,e'.symm_apply_apply]
  refine ⟨e',c,?_,?_,hc,hco,ha⟩
  · rw [hez'];exact hz
  · rw [het'];exact ht

end CFSG.Quasithin.ChapterJ.RuSubgroup

module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.BlockRecognition.Radical
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.Commutator.CentralizingComplement
/-!
# Identifying the original residual actor

For every marked source field, including F₂, F*(H*) equals O²(H*).
Its full preimage is therefore O²(H)O₂(H) once the commutator bound has
identified the kernel. The original fixed denominator is consequently
exactly the centralizer of O²(H) in the moved subgroup.

Source: Aschbacher–Smith C.1.17–18, printed p.126; Campbell II.8, p.38.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

theorem localStar_fitting_eq_residual (h : InLocalClass e) (hB : IsBaumannFixed B) :
    generalizedFitting (LocalStar e)=pResidual 2 (LocalStar e) := by
  obtain ⟨n,hn,F,_,_,_,hF,⟨m⟩⟩ := h.natural
  have htwo : 2≤Nat.card F := Finite.one_lt_card
  rcases htwo.eq_or_lt with h2|h2
  · have h3:=m.actor_card_of_field_card_two e h2.symm
    have h6:=h.localStar_card_six_of_field_card_two m h2.symm
    apply le_antisymm ?_ ?_
    · intro a ha
      apply mem_pResidual_of_orderOf_coprime
      apply (by decide : Nat.Coprime 2 3).of_dvd_right
      have hd:=orderOf_dvd_natCard (⟨a,ha⟩:generalizedFitting (LocalStar e))
      simpa only [←Subgroup.orderOf_coe,h3] using hd
    · apply sInf_le
      refine ⟨inferInstance,IsPGroup.of_card (n:=1) ?_⟩
      have hh := (generalizedFitting (LocalStar e)).card_mul_index
      rw [h3,h6] at hh
      change (generalizedFitting (LocalStar e)).index=2^1
      omega
  · have ht:=h.generalizedFitting_localStar_eq_top hB m h2
    rw [ht]
    symm
    apply (pResidual_eq_top_iff 2 _).mpr
    obtain ⟨E⟩:=h.localStar_equiv_psl hB m
    let : Group.IsPerfect PSL(2,F) := ⟨derived_psl_eq_top_of_two_lt_card h2⟩
    let : Group.IsPerfect (LocalStar e) := Group.IsPerfect.ofSurjective (f:=E.symm.toMonoidHom) E.symm.surjective
    intro N hN hp
    let := hN
    have : Subsingleton ((LocalStar e)⧸N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

theorem actorLift_eq_residual_sup_core_of_bound (h : InLocalClass e) (hB : IsBaumannFixed B)
    (hcomm : ⁅pResidual 2 H,pCore 2 H⁆≤Campbell.V H) :
    actorLift e=pResidual 2 H⊔pCore 2 H := by
  unfold actorLift
  rw [localStar_fitting_eq_residual h hB,comap_pResidual_quotient,
    kernel_eq_core_of_residual_commutator_le h hB hcomm]

theorem movedFixed_eq_residual_centralizer_of_bound (h : InLocalClass e) (hB : IsBaumannFixed B)
    (hcomm : ⁅pResidual 2 H,pCore 2 H⁆≤Campbell.V H) :
    movedFixed e=(centralizer (pResidual 2 H:Set H)).subgroupOf (moved e) := by
  ext x
  change (∀g∈actorLift e,g*(x:H)=(x:H)*g)↔∀g∈pResidual 2 H,g*(x:H)=(x:H)*g
  constructor
  · intro hx g hg
    apply hx g
    rw [actorLift_eq_residual_sup_core_of_bound h hB hcomm]
    exact (show pResidual 2 H≤pResidual 2 H⊔pCore 2 H from le_sup_left) hg
  · intro hx g hg
    rw [actorLift_eq_residual_sup_core_of_bound h hB hcomm] at hg
    obtain ⟨l,hl,q,hq,rfl⟩:=mem_sup_of_normal_left.mp hg
    have hqx : q*(x:H)=(x:H)*q :=
      ((mem_omegaOneCenterAmbient_iff _ _).mp (h.moved_le_coreOmegaCenter x.property)).2.2 q hq
    rw [mul_assoc,hqx,←mul_assoc,hx l hl,mul_assoc]
end CFSG.Quasithin.ChapterC.GlaubermanNiles

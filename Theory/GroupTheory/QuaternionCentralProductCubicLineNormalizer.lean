module

public import Theory.GroupTheory.QuaternionCentralProductInvertingCubics
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Bounding a cubic-axis normalizer in a quaternion-product local group

The factor swap gives an index-two stabilizer of the quaternion support.
Its quotient by the core has order18, while the cubic-axis normalizer meets
the core in its quaternion fixed factor of order8. The actual normalizer
therefore has order dividing144. No subgroup enumeration is used.
Source: Aschbacher, *Sporadic Groups* (1994),45.8,printed p245.
-/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem cubic_line_normalizer_card_dvd_of_quaternion_swap
    (H B C W:Subgroup G) (hH:Nat.card H=1152)
    (hB:Nonempty (B≃*QuaternionGroup 2)) (hC:Nonempty (C≃*QuaternionGroup 2))
    (hi:Nat.card (B⊓C:Subgroup G)=2) (hcomm:∀b∈B,∀c∈C,b*c=c*b)
    (hQH:B⊔C≤H) (hHN:H≤normalizer (B⊔C:Subgroup G))
    (hW:Nat.card W=3) (hWH:W≤H) (hfixed:(B⊔C)⊓centralizer (W:Set G)=C)
    (s:G) (hs:s∈H) (hsB:B.map (MulAut.conj s).toMonoidHom=C)
    (hsC:C.map (MulAut.conj s).toMonoidHom=B) :
    Nat.card (H⊓normalizer (W:Set G):Subgroup G)∣144 := by
  let Q:=B⊔C
  let F:=H⊓normalizer (C:Set G)
  let N:=H⊓normalizer (W:Set G)
  have hBcard:Nat.card B=8:=by rw [Nat.card_congr hB.some.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hCcard:Nat.card C=8:=by rw [Nat.card_congr hC.some.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hBC:B≠C:=by intro he; rw [←he,inf_idem,hBcard] at hi; omega
  have hFindex:F.relIndex H=2:=by
    apply relIndex_eq_two_iff_exists_notMem_and'.mpr
    refine ⟨s,hs,?_,?_⟩
    · exact fun hh=>hBC ((mem_normalizer_iff_map_conj_eq.mp hh.2).symm.trans hsC).symm
    · intro g hg
      have hmap:Q.map (MulAut.conj g).toMonoidHom=Q:=mem_normalizer_iff_map_conj_eq.mp (hHN hg)
      have him:=quaternion_subgroup_eq_factor B C (C.map (MulAut.conj g).toMonoidHom) hB hC hi hcomm
        ⟨(C.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans hC.some⟩
        ((map_mono le_sup_right).trans_eq hmap)
      rcases him with hCB|hCC
      · left
        refine ⟨H.mul_mem hs hg,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
        have hcomp:(MulAut.conj (s*g)).toMonoidHom=(MulAut.conj s).toMonoidHom.comp (MulAut.conj g).toMonoidHom:=by
          ext x
          change (s*g)*x*(s*g)⁻¹=s*(g*x*g⁻¹)*s⁻¹
          group
        change C.map (MulAut.conj (s*g)).toMonoidHom=C
        rw [hcomp,←map_map,hCB,hsB]
      · exact Or.inr ⟨hg,mem_normalizer_iff_map_conj_eq.mpr hCC⟩
  have hFcard:Nat.card F=576:=by
    have hh:=relIndex_mul_relIndex (⊥:Subgroup G) F H bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hFindex,hH] at hh
    omega
  have hCQ:C≤Q:=le_sup_right
  have hQC:Q≤normalizer (C:Set G):=sup_le
    ((show B≤centralizer (C:Set G) from fun b hb c hc=>(hcomm b hb c hc).symm).trans
      (centralizer_le_normalizer _)) C.le_normalizer
  have hQF:Q≤F:=le_inf hQH hQC
  have hQcard:Nat.card Q=32:=by
    have hh:=card_mul_eq_card_inf_mul_card_sup_of_normalizes B C
      ((show C≤centralizer (B:Set G) from fun c hc b hb=>hcomm b hb c hc).trans (centralizer_le_normalizer _))
    rw [hBcard,hCcard,hi] at hh
    change 8*8=2*Nat.card Q at hh
    omega
  have hQindex:Q.relIndex F=18:=by
    have hh:=relIndex_mul_relIndex (⊥:Subgroup G) Q F bot_le hQF
    rw [relIndex_bot_left,relIndex_bot_left,hQcard,hFcard] at hh
    omega
  have hNF:N≤F:=by
    intro g hg
    refine ⟨hg.1,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    have hq:(B⊔C).map (MulAut.conj g).toMonoidHom=B⊔C:=mem_normalizer_iff_map_conj_eq.mp (hHN hg.1)
    have hw:(centralizer (W:Set G)).map (MulAut.conj g).toMonoidHom=centralizer (W:Set G):=
      mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_centralizer W hg.2)
    calc
      C.map (MulAut.conj g).toMonoidHom=((B⊔C)⊓centralizer (W:Set G)).map (MulAut.conj g).toMonoidHom :=congrArg _ hfixed.symm
      _ = C:=by rw [map_inf _ _ _ (MulAut.conj g).injective,hq,hw,hfixed]
  have hQNW:Q⊓normalizer (W:Set G)≤centralizer (W:Set G):=by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    have hd:Q⊓W=⊥:=disjoint_iff.mp (disjoint_of_coprime_natCard (by rw [hQcard,hW];decide))
    rw [←hd]
    refine le_inf ?_ (le_normalizer_iff_commutator_le_right.mp inf_le_right)
    exact (commutator_mono inf_le_left le_rfl).trans (le_normalizer_iff_commutator_le_left.mp (hWH.trans hHN))
  have hQN:Q⊓N=C:=by
    apply le_antisymm
    · rw [←hfixed]
      exact le_inf inf_le_left (fun g hg=>hQNW ⟨hg.1,hg.2.2⟩)
    · intro g hg
      have hc:=hfixed.ge hg
      exact ⟨hc.1,hQH hc.1,centralizer_le_normalizer _ hc.2⟩
  let : (Q.subgroupOf F).Normal:=(normal_subgroupOf_iff_le_normalizer hQF).mpr
    (inf_le_left.trans hHN)
  have hd:=relIndex_dvd_index_of_normal (Q.subgroupOf F) (N.subgroupOf F)
  rw [relIndex_subgroupOf hNF] at hd
  change Q.relIndex N∣Q.relIndex F at hd
  rw [hQindex] at hd
  have hcN:=relIndex_mul_relIndex (⊥:Subgroup G) (Q⊓N) N bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,hQN,hCcard] at hcN
  have he:8*(Q.relIndex N)=Nat.card N:=hcN
  rw [←he]
  exact Nat.mul_dvd_mul_left 8 hd
end Subgroup

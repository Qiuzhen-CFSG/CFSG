module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowFixers
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowCenter
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AlternatingSixMovementSource
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.FourMovementSource
public import Theory.GroupTheory.GeneralizedFitting.SylowCentralizerSchreier
/-! # Central Sylow elements act by the component Sylow center
An element centralizing a nontrivial component Sylow cannot move its
centerless component to a distinct commuting component. Its resulting action
is inner by the same Sylow in every non-A₆ model. For A₆, the actual parabolic
interchange supplies a moving four-group, and the proved automorphism-Sylow
center theorem gives the same conclusion. This retains the original component
even when it is not normal in H, supplying both branches of 2.5.8(4).
Source: Aschbacher--Smith, printed pp.556--557.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {J:Type*} [Group J] [Finite J]

theorem component_center_action_inner
    (S:Sylow 2 J) (D:Subgroup J) (hD:IsComponent J D)
    (hc:center D=⊥) (P:Sylow 2 D) (hP:(P:Subgroup D)=(S:Subgroup J).subgroupOf D)
    (hPc:Nat.card (center P)=2)
    (hcases:SylowPointwiseFixersInner D ∨
      ∃_e:D≃*alternatingGroup (Fin 6),∃E:Subgroup D,IsKleinFour E ∧ E≤P ∧
        ∃s:normalizer (D:Set J),(s:J)∈S ∧ E.map (D.normalizerMonoidHom s).toMonoidHom≠E)
    (y:J) (hy:y∈centerIn (S:Subgroup J)) :
    ∃u:D,u∈P ∧ (∀v:D,v∈P→v*u=u*v) ∧
      ∀k:D,((u*k*u⁻¹:D):J)=y*(k:J)*y⁻¹ := by
  have hne:(P:Subgroup D)≠⊥:=by
    intro hb
    have hh:Nat.card P=1:=(P:Subgroup D).eq_bot_iff_card.mp hb
    have hd:= (center P).card_subgroup_dvd_card
    rw [hPc,hh] at hd
    norm_num at hd
  have hYN:y∈normalizer (D:Set J):=by
    apply mem_normalizer_iff_map_conj_eq.mpr
    by_contra hn
    have hcomm:=commutator_eq_bot_iff_le_centralizer.mp
      (hD.commutator_eq_bot_of_ne (hD.map_conj y) (Ne.symm hn))
    apply hne
    apply bot_unique
    intro u hu
    have hfix:y*(u:J)*y⁻¹=u:=by rw [←hy.2 u (show u∈(S:Subgroup J).subgroupOf D from hP ▸ hu),mul_inv_cancel_right]
    have hconj:(u:J)∈D.map (MulAut.conj y).toMonoidHom:=hfix ▸ mem_map_of_mem (MulAut.conj y).toMonoidHom u.property
    have huC:u∈center D:=mem_center_iff.mpr (fun k=>Subtype.ext (hcomm k.property u hconj).symm)
    exact hc ▸ huC
  let N:=(S:Subgroup J)⊓normalizer (D:Set J)
  let f:N→*MulAut D:=D.normalizerMonoidHom.comp (inclusion inf_le_right)
  let A:=f.range
  have hA:IsPGroup 2 A:= (S.isPGroup'.to_le (show N≤S from inf_le_left)).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let yn:N:=⟨y,hy.1,hYN⟩
  let a:=f yn
  have ha:∀u∈P,a u=u:=by
    intro u hu
    apply Subtype.ext
    change y*(u:J)*y⁻¹=u
    rw [←hy.2 u (show u∈(S:Subgroup J).subgroupOf D from hP ▸ hu),mul_inv_cancel_right]
  have hPA:(P:Subgroup D).map MulAut.conj≤A:=by
    rintro _ ⟨u,hu,rfl⟩
    refine ⟨⟨u,(show u∈(S:Subgroup J).subgroupOf D from hP ▸ hu),D.le_normalizer u.property⟩,?_⟩
    ext k
    rfl
  have hinner:∃u∈P,a=MulAut.conj u:=by
    rcases hcases with hi|⟨e,E,hE,hEP,s,hs,hm⟩
    · exact hi P a ha
    let :=hE
    have hmove:∃b∈A,E.map b.toMonoidHom≠E:=
      ⟨D.normalizerMonoidHom s,⟨⟨s,hs,s.property⟩,rfl⟩,hm⟩
    have hac:a∈(center A).map A.subtype:=by
      refine ⟨⟨a,⟨yn,rfl⟩⟩,mem_center_iff.mpr ?_,rfl⟩
      rintro ⟨b,⟨n,rfl⟩⟩
      apply Subtype.ext
      change f n*f yn=f yn*f n
      rw [←map_mul,←map_mul]
      apply congrArg f
      exact Subtype.ext (hy.2 n n.property.1)
    obtain ⟨u,hu,he⟩:=AlternatingSix.ShadowLocal.center_inner_of_four_movement_of_equiv
      e P A hA hPA E hEP hmove hac
    exact ⟨u,hu,he.symm⟩
  obtain ⟨u,hu,he⟩:=hinner
  refine ⟨u,hu,?_,?_⟩
  · intro v hv
    have hh:=ha v hv
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro k
    exact (congrArg Subtype.val (DFunLike.congr_fun he k)).symm
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.center_action_inner
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel L)
    (y:G) (hy:y∈centerIn ((S:Subgroup H).map H.subtype)) :
    ∃u:L,(u:G)∈(S:Subgroup H).map H.subtype ∧
      (∀v:L,(v:G)∈(S:Subgroup H).map H.subtype→v*u=u*v) ∧
      ∀k:L,((u*k*u⁻¹:L):G)=y*(k:G)*y⁻¹ := by
  let D:=L.subgroupOf H
  let eD:D≃*L:=subgroupOfEquivOfLe c.component_le
  let : IsSimpleGroup L:=MathieuSourceSetup.component_simple c hG hempty hgen
  let : IsSimpleGroup D:=eD.isSimpleGroup
  let :=c.component.2
  have hc:center D=⊥:=center_eq_bot_of_simple_perfect
  obtain ⟨R,hR⟩:=S.exists_subgroupOf_eq_of_subnormal D c.component.1
  let P:=R.mapSurjective (f:=eD.toMonoidHom) eD.surjective
  let eR:R≃*P:=(R:Subgroup D).equivMapOfInjective eD.toMonoidHom eD.injective
  have hm:=MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  have hPc:Nat.card (center R)=2:=(Nat.card_congr (centerCongr eR).toEquiv).trans
    (hm.sylowTwoShape P).center_card
  have hcases:SylowPointwiseFixersInner D ∨
      ∃_e:D≃*alternatingGroup (Fin 6),∃E:Subgroup D,IsKleinFour E ∧ E≤R ∧
        ∃s:normalizer (D:Set H),(s:H)∈S ∧ E.map (D.normalizerMonoidHom s).toMonoidHom≠E:=by
    rcases hm.alternatingSix_or_sylowPointwiseFixersInner with he|hi
    · obtain ⟨e⟩:=he
      obtain ⟨E,hE,hES,s,hs,hm⟩:=alternating_six_four_movement_source c.gamma hempty S
        (c.hypotheses115 hG).mem_HeOver.2.2 D c.component
        ((c.hypotheses115 hG).component_inputs D c.component).1 (eD.trans e)
      exact Or.inr ⟨eD.trans e,E,hE,hR.symm ▸ hES,s,hs,hm⟩
    · exact Or.inl (hi.of_mulEquiv eD)
  obtain ⟨yH,hyS,rfl⟩:=hy.1
  have hyH:yH∈centerIn (S:Subgroup H):=by
    refine ⟨hyS,?_⟩
    intro s hs
    exact Subtype.ext (hy.2 s (mem_map_of_mem H.subtype hs))
  obtain ⟨u,hu,huc,ha⟩:=component_center_action_inner S D c.component hc R hR hPc hcases yH hyH
  refine ⟨eD u,mem_map_of_mem H.subtype (show u∈(S:Subgroup H).subgroupOf D from hR ▸ hu),?_,?_⟩
  · intro v hv
    obtain ⟨s,hs,he⟩:=hv
    have hvR:eD.symm v∈R:=by
      change eD.symm v∈(R:Subgroup D)
      rw [hR]
      change (⟨(v:G),c.component_le v.property⟩:H)∈S
      have heq:s=(⟨(v:G),c.component_le v.property⟩:H):=Subtype.ext he
      exact heq ▸ hs
    simpa only [map_mul,eD.apply_symm_apply] using congrArg eD (huc (eD.symm v) hvR)
  · intro k
    exact congrArg Subtype.val (ha (eD.symm k))
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

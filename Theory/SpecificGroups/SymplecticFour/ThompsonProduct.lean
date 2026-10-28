module
public import Theory.SpecificGroups.SymplecticFour.ThompsonInner
/-! # The Thompson product for a normal binary symplectic component
The root-wing comparison makes the Thompson action inner. Each of the two
q³ wings then joins a maximum elementary action-kernel intersection without
loss of order, placing both wings and their generated component Sylow in J(S).
Sylow maximality splits the inner actors into the component and centralizer.
Source: Aschbacher--Smith 2.5.7, printed pp.554--555.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour.ThompsonInner
open CentralRootGeometry
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
theorem thompson_le_sylow_component_centralizer
    (K:Subgroup G) [K.Normal] (e:K≃*(Sp F))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G) :
    Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) ≤
      ((S:Subgroup G)⊓K) ⊔ ((S:Subgroup G)⊓centralizer (K:Set G)) := by
  let f := action K e
  have hi := thompson_action_inner K e hn hF S
  have hJS : Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) ≤ (S:Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hq : center (Sp F)=⊥ := EvenProjective.center_eq_bot
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal K
  let R' := R.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hRI : (R':Subgroup (Sp F)).map (MulAut.conj : (Sp F)→*MulAut (Sp F)) ≤
      (S:Subgroup G).map f := by
    rintro _ ⟨b,⟨k,hk,rfl⟩,rfl⟩
    refine ⟨(k:G), ?_, ?_⟩
    · have hh : k∈(S:Subgroup G).subgroupOf K := hR ▸ hk
      exact hh
    · exact action_on_K K e k
  intro x hx
  obtain ⟨b,hb⟩ := hi (mem_map_of_mem f hx)
  have hbR : b∈R' := MulAut.inner_mem_image_sylow hq R'
    ((S:Subgroup G).map f) (S.isPGroup'.map f) hRI
    (hb ▸ mem_map_of_mem f (hJS hx))
  obtain ⟨k,hk,hke⟩ := hbR
  have hkS : (k:G)∈(S:Subgroup G) := by
    have hh : k∈(S:Subgroup G).subgroupOf K := hR ▸ hk
    exact hh
  have hfx : f x=f k := by
    change e k=b at hke
    rw [action_on_K, hke]
    exact hb.symm
  have hker : (k:G)⁻¹*x∈f.ker := by
    change f ((k:G)⁻¹*x)=1
    rw [map_mul,map_inv,hfx,inv_mul_cancel]
  have hc : (k:G)⁻¹*x∈centralizer (K:Set G) :=
    action_ker_eq K e ▸ hker
  have hs : (k:G)⁻¹*x∈(S:Subgroup G) := S.mul_mem (S.inv_mem hkS) (hJS hx)
  have hprod := (((S:Subgroup G)⊓K) ⊔ ((S:Subgroup G)⊓centralizer (K:Set G))).mul_mem
    (mem_sup_left ⟨hkS,k.property⟩) (mem_sup_right ⟨hs,hc⟩)
  simpa using hprod

theorem sylow_component_le_thompson
    (K:Subgroup G) [K.Normal] (e:K≃*(Sp F))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G) :
    (S:Subgroup G)⊓K ≤ Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) := by
  let f := action K e
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal K
  let R' := R.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hrmap : (R:Subgroup K).map K.subtype = (S:Subgroup G)⊓K := by
    rw [hR, subgroupOf_map_subtype]
  let eU : (unipotent (F:=F)) ≃* ↥((S:Subgroup G)⊓K) :=
    ((Sylow.equiv (unipotentSylow hF (by omega)) R').trans
      ((R:Subgroup K).equivMapOfInjective e.toMonoidHom e.injective).symm).trans
      (((R:Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
        (MulEquiv.subgroupCongr hrmap))
  let j : (unipotent (F:=F))→*G := ((S:Subgroup G)⊓K).subtype.comp eU.toMonoidHom
  have hj : Function.Injective j := Subtype.val_injective.comp eU.injective
  have hjK (u:(unipotent (F:=F))) : j u∈K := (eU u).property.2
  have hq : center (Sp F)=⊥ := EvenProjective.center_eq_bot
  have hfi : Function.Injective (f.comp j) := by
    intro a b hab
    have ha := action_on_K K e (⟨j a,hjK a⟩:K)
    have hb := action_on_K K e (⟨j b,hjK b⟩:K)
    change action K e (j a)=action K e (j b) at hab
    rw [ha,hb] at hab
    exact hj (congrArg (fun z:K => (z:G)) (e.injective
      (MulAut.conj_injective_of_center_eq_bot hq hab)))
  obtain ⟨A,hA⟩ := Stellmacher.elementaryAbelianMaxSubgroups_nonempty (S:Subgroup G)
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hi := maxElementary_action_inner K e hn hF S A hA
  let eI : (Sp F)≃*MulAut.innerSubgroup (Sp F) :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hq)
  have hrI : primeRank 2 (MulAut.innerSubgroup (Sp F))=3*n :=
    (primeRank_equiv 2 eI).symm.trans (EvenTwoRank.rank hF (by omega))
  have hcA : Nat.card (A.map f)≤(Nat.card F)^3 := by
    let B := (A.map f).subgroupOf (MulAut.innerSubgroup (Sp F))
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hi
    have hb := (primeRank_le_iff_elementary_card_le (MulAut.innerSubgroup (Sp F))).mp
      hrI.le B inferInstance
    rw [Nat.card_congr (subgroupOfEquivOfLe hi).toEquiv] at hb
    simpa only [hF,←pow_mul,Nat.mul_comm n 3] using hb
  have hplane (V:Subgroup ((unipotent (F:=F)))) [IsElementaryAbelian 2 V]
      (hv:Nat.card V=(Nat.card F)^3) :
      V.map j≤Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) := by
    let : IsElementaryAbelian 2 (V.map j) := IsElementaryAbelian.map j
    apply Stellmacher.elementary_le_maxJ_of_image_bound (S:Subgroup G) A (V.map j) f hA
    · rintro _ ⟨u,hu,rfl⟩
      exact (eU u).property.1
    · rintro _ ⟨u,hu,rfl⟩ a ha
      have haC : a∈centralizer (K:Set G) := action_ker_eq K e ▸ ha.2
      exact (haC _ (hjK u)).symm
    · apply disjoint_iff.mpr
      apply bot_unique
      rintro _ ⟨⟨u,hu,rfl⟩,huk⟩
      have huone : u=1 := hfi (show (f.comp j) u=(f.comp j) 1 from
        (show f (j u)=1 from huk).trans (map_one _).symm)
      simp only [huone,map_one,mem_bot]
    · rw [card_map_of_injective hj,hv]
      exact hcA
  let : IsElementaryAbelian 2 (wing (F:=F) false):=wing_elementary false
  let : IsElementaryAbelian 2 (wing (F:=F) true):=wing_elementary true
  have h1:=hplane (wing (F:=F) false) (card_wing false)
  have h2:=hplane (wing (F:=F) true) (card_wing true)
  have hall : (⊤:Subgroup (unipotent (F:=F))).map j≤
      Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) := by
    rw [←wings_generate,Subgroup.map_sup]
    exact sup_le h1 h2
  have hju (u:unipotent (F:=F)) : j u∈Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) :=
    hall (mem_map_of_mem j (mem_top u))
  intro x hx
  have hh := hju (eU.symm ⟨x,hx⟩)
  change ((eU (eU.symm ⟨x,hx⟩)):G) ∈ _ at hh
  simpa only [eU.apply_symm_apply] using hh

/-- The literal Thompson product in the symplectic branch of 2.5.7. -/
theorem thompson_eq_sylow_component_sup_centralizer
    (K:Subgroup G) [K.Normal] (e:K≃*(Sp F))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G) :
    Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) =
      ((S:Subgroup G)⊓K) ⊔
        (Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)⊓centralizer (K:Set G)) := by
  let J:=Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)
  let SK:=(S:Subgroup G)⊓K
  let SC:=(S:Subgroup G)⊓centralizer (K:Set G)
  have hKJ : SK≤J := sylow_component_le_thompson K e hn hF S
  have hnC : SC≤normalizer (SK:Set G) :=
    (inf_le_right.trans (centralizer_le (show SK≤K from inf_le_right))).trans
      (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm ?_ (sup_le hKJ inf_le_left)
  intro x hx
  have hp : x∈(SK:Set G)*(SC:Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left SK SC hnC]
    exact thompson_le_sylow_component_centralizer K e hn hF S hx
  obtain ⟨k,hk,c,hc,hkc⟩ := hp
  have hcJ : c∈J := by
    have hh := J.mul_mem (J.inv_mem (hKJ hk)) hx
    rw [←hkc,inv_mul_cancel_left] at hh
    exact hh
  rw [←hkc]
  exact (SK⊔(J⊓centralizer (K:Set G))).mul_mem
    (mem_sup_left hk) (mem_sup_right ⟨hcJ,hc.2⟩)

end Theory.SpecificGroups.SymplecticFour.ThompsonInner

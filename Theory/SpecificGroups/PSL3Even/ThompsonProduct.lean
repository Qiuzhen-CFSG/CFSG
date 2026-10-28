module
public import Theory.SpecificGroups.PSL3Even.ThompsonInner
public import Theory.GroupTheory.SylowInnerAction
public import Theory.SpecificGroups.PSL3Even.TwoRank
/-! # The Thompson product for a normal binary linear component
The root-plane comparison puts all maximum elementary actors inside the inner
action. Both root planes can themselves be joined to an actual action-kernel
intersection without decreasing maximum elementary order, so the component
Sylow lies in J(S). Sylow maximality then splits every inner actor into its
component-Sylow factor and centralizer factor. This proves the literal product,
without assuming the Thompson subgroup contains the component Sylow.
Source: Aschbacher--Smith 2.5.7, printed pp.554--555. -/
public section
open Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.PSL3Even.ThompsonInner
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F]
theorem thompson_le_sylow_component_centralizer
    (K:Subgroup G) [K.Normal] (e:K≃*PSL(3,F))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G) :
    Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) ≤
      ((S:Subgroup G)⊓K) ⊔ ((S:Subgroup G)⊓centralizer (K:Set G)) := by
  let f := action K e
  have hi := thompson_action_inner K e hn hF S
  have hJS : Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) ≤ (S:Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hq : center PSL(3,F)=⊥ := by
    let := Atlas.sl_perfect (F:=F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal K
  let R' := R.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hRI : (R':Subgroup PSL(3,F)).map (MulAut.conj : PSL(3,F)→*MulAut PSL(3,F)) ≤
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

open PSL3.LinearThree UnipotentGeometry Theory.GroupTheory in
theorem sylow_component_le_thompson
    (K:Subgroup G) [K.Normal] (e:K≃*PSL(3,F))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G) :
    (S:Subgroup G)⊓K ≤ Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) := by
  let : CharP F 2 := by
    let := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by simpa only [←Nat.card_eq_fintype_card] using hF)
  let f := action K e
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal K
  let R' := R.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hrmap : (R:Subgroup K).map K.subtype = (S:Subgroup G)⊓K := by
    rw [hR, subgroupOf_map_subtype]
  let eU : U F ≃* ↥((S:Subgroup G)⊓K) :=
    (((unipotentEquiv F).trans (Sylow.equiv (unipotentSylow F (by omega) hF) R')).trans
      ((R:Subgroup K).equivMapOfInjective e.toMonoidHom e.injective).symm).trans
      (((R:Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
        (MulEquiv.subgroupCongr hrmap))
  let j : U F→*G := ((S:Subgroup G)⊓K).subtype.comp eU.toMonoidHom
  have hj : Function.Injective j := Subtype.val_injective.comp eU.injective
  have hjK (u:U F) : j u∈K := (eU u).property.2
  have hq : center PSL(3,F)=⊥ := by
    let := Atlas.sl_perfect (F:=F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
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
  let eI : PSL(3,F)≃*MulAut.innerSubgroup PSL(3,F) :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hq)
  have hrI : primeRank 2 (MulAut.innerSubgroup PSL(3,F))=2*n :=
    (primeRank_equiv 2 eI).symm.trans (Matrix.PSL3Even.two_rank F (by omega) hF)
  have hcA : Nat.card (A.map f)≤(Nat.card F)^2 := by
    let B := (A.map f).subgroupOf (MulAut.innerSubgroup PSL(3,F))
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hi
    have hb := (primeRank_le_iff_elementary_card_le (MulAut.innerSubgroup PSL(3,F))).mp
      hrI.le B inferInstance
    rw [Nat.card_congr (subgroupOfEquivOfLe hi).toEquiv] at hb
    simpa only [hF,←pow_mul,Nat.mul_comm n 2] using hb
  have hplane (V:Subgroup (U F)) [IsElementaryAbelian 2 V]
      (hv:Nat.card V=(Nat.card F)^2) :
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
  have h1:=hplane (V₁ F) (card_V₁ F)
  have h2:=hplane (V₂ F) (card_V₂ F)
  have hju (u:U F) : j u∈Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) := by
    have hu : u=(⟨0,u.y,u.c⟩:U F)*(⟨u.x,0,0⟩:U F) := by
      apply U.ext <;> simp
    rw [hu,map_mul]
    exact (Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)).mul_mem
      (h2 (mem_map_of_mem j ((mem_V₂ F _).mpr rfl)))
      (h1 (mem_map_of_mem j ((mem_V₁ F _).mpr rfl)))
  intro x hx
  have hh := hju (eU.symm ⟨x,hx⟩)
  change ((eU (eU.symm ⟨x,hx⟩)):G) ∈ _ at hh
  simpa only [eU.apply_symm_apply] using hh

/-- The literal Thompson product in the centerless linear branch of 2.5.7. -/
theorem thompson_eq_sylow_component_sup_centralizer
    (K:Subgroup G) [K.Normal] (e:K≃*PSL(3,F))
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

end Matrix.PSL3Even.ThompsonInner


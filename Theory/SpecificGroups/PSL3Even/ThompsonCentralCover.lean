module
public import Theory.SpecificGroups.PSL3Even.ThompsonInner
public import Theory.GroupTheory.MaxElementaryImageComparison.CentralKernel
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.GroupTheory.SylowInnerAction
/-! # Thompson products through an elementary central linear cover
For a normal perfect cover of PSL3(2^n), the original central quotient action
has ordinary centralizer kernel. If elementary model subgroups have elementary
full preimages, the two root planes exclude all maximum elementary outer
actors. Those actors then centralize the covering center, so maximality absorbs
the center into each maximum elementary subgroup. The exact kernel/image order
formula promotes both lifted planes to J(S), giving the literal Sylow product.
The exceptional PSL3(4) source discharges the elementary-preimage hypothesis
using the proved I.2.2(3b) cover theorem.
Source: Aschbacher--Smith 2.5.7, printed pp.554--555. -/
public section
open Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.PSL3Even.ThompsonCentralCover
open PSL3.LinearThree UnipotentGeometry
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F]
noncomputable def projection (K:Subgroup G) (e:K ⧸ center K≃*PSL(3,F)) : K→*PSL(3,F) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center K))
omit [Finite G] [Finite F] in
theorem projection_apply (K:Subgroup G) (e:K ⧸ center K≃*PSL(3,F)) (k:K) :
    projection K e k=e (QuotientGroup.mk' (center K) k) := by
  exact congrArg (fun f:K→*PSL(3,F)=>f k)
    (show projection K e=e.toMonoidHom.comp (QuotientGroup.mk' (center K)) from rfl)

omit [Finite G] [Finite F] in
theorem projection_surjective (K:Subgroup G) (e:K ⧸ center K≃*PSL(3,F)) :
    Function.Surjective (projection K e) := e.surjective.comp (QuotientGroup.mk'_surjective _)
omit [Finite G] [Finite F] in
theorem projection_ker (K:Subgroup G) (e:K ⧸ center K≃*PSL(3,F)) :
    (projection K e).ker=center K := by
  rw [projection,MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
noncomputable def action (K:Subgroup G) [K.Normal] (e:K ⧸ center K≃*PSL(3,F)) : G→*MulAut PSL(3,F) :=
  (MulAut.centralQuotientAction e).comp (MulAut.conjNormal : G→*MulAut K)
omit [Finite G] [Finite F] in
theorem action_on_K (K:Subgroup G) [K.Normal] (e:K ⧸ center K≃*PSL(3,F)) (k:K) :
    action K e k=MulAut.conj (projection K e k) := by
  change MulAut.centralQuotientAction e (MulAut.conjNormal (k:G))=_
  have hk : (MulAut.conjNormal (k:G):MulAut K)=MulAut.conj k := by ext y; rfl
  rw [hk,MulAut.centralQuotientAction_conj]
  rfl

omit [Finite G] [Finite F] in
theorem action_ker_eq (K:Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e:K ⧸ center K≃*PSL(3,F)) : (action K e).ker=centralizer (K:Set G) := by
  ext a
  constructor
  · intro ha y hy
    have he : MulAut.conjNormal a=1 := (MulAut.centralQuotientAction_injective e)
      (show MulAut.centralQuotientAction e (MulAut.conjNormal a)=MulAut.centralQuotientAction e 1 from by
        change (action K e) a=(MulAut.centralQuotientAction e) 1
        rw [map_one]
        exact ha)
    have hh := congrArg (fun b:MulAut K=>(b ⟨y,hy⟩:G)) he
    change a*y*a⁻¹=y at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro ha
    change (MulAut.centralQuotientAction e) (MulAut.conjNormal a)=1
    rw [← (MulAut.centralQuotientAction e).map_one]
    congr 1
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change a*(y:G)*a⁻¹=(y:G)
    rw [←ha y y.property,mul_inv_cancel_right]

theorem maxElementary_action_inner (K:Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e:K ⧸ center K≃*PSL(3,F)) (hZ:IsPGroup 2 (center K))
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W →
      IsElementaryAbelian 2 (W.comap (projection K e)))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G)
    (A:Subgroup G) (hA:A∈Stellmacher.elementaryAbelianMaxSubgroups (S:Subgroup G)) :
    A.map (action K e)≤MulAut.innerSubgroup PSL(3,F) := by
  let : CharP F 2 := by
    let := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by simpa only [←Nat.card_eq_fintype_card] using hF)
  let q:=projection K e
  let f:=action K e
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal K
  let P:=R.mapSurjective (f:=q) (projection_surjective K e)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F)
    (unipotentSylow F (by omega) hF) P
  let j:U F→*PSL(3,F):=(MulAut.conj g).toMonoidHom.comp (projective F)
  let W:=(V₁ F).map j
  let V:=(W.comap q).map K.subtype
  have hWP : W≤(P:Subgroup PSL(3,F)) := by
    rintro _ ⟨u,hu,rfl⟩
    have hh := congrArg Sylow.toSubgroup hg
    rw [←hh]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom ((projective_range F).le ⟨u,rfl⟩)
  have hkerR : q.ker≤(R:Subgroup K) := by
    rw [projection_ker]
    exact hZ.le_sylow_of_normal R
  have hVS : V≤(S:Subgroup G) := by
    rintro _ ⟨k,hk,rfl⟩
    have hk' : k∈((R:Subgroup K).map q).comap q := hWP hk
    rw [comap_map_eq_self hkerR,hR] at hk'
    exact hk'
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map j
  let : IsElementaryAbelian 2 (W.comap q) := hlift W inferInstance
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map K.subtype
  have hc : V≤centralizer (A⊓f.ker:Set G) := by
    rintro _ ⟨k,hk,rfl⟩ a ha
    have haC : a∈centralizer (K:Set G) := action_ker_eq K e ▸ ha.2
    exact (haC _ k.property).symm
  have hq : center PSL(3,F)=⊥ := by
    let := Atlas.sl_perfect (F:=F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
  have hfc : f.comp K.subtype=(MulAut.conj : PSL(3,F)→*MulAut PSL(3,F)).comp q := by
    apply MonoidHom.ext
    intro k
    exact action_on_K K e k
  have hVm : V.map f=W.map (MulAut.conj : PSL(3,F)→*MulAut PSL(3,F)) := by
    rw [show V.map f=(W.comap q).map (f.comp K.subtype) from Subgroup.map_map _ _ _,hfc,
      ←Subgroup.map_map,map_comap_eq_self_of_surjective (projection_surjective K e)]
  have hv : Nat.card (V.map f)=(Nat.card F)^2 := by
    rw [hVm,card_map_of_injective (MulAut.conj_injective_of_center_eq_bot hq)]
    rw [show W=(V₁ F).map j from rfl,card_map_of_injective
      ((MulAut.conj g).injective.comp (projective_injective F)),card_V₁]
  exact Stellmacher.maxElementary_psl3_image_inner hn hF (S:Subgroup G) A V f hA hVS hc hv

theorem thompson_action_inner (K:Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e:K ⧸ center K≃*PSL(3,F)) (hZ:IsPGroup 2 (center K))
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W →
      IsElementaryAbelian 2 (W.comap (projection K e)))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G) :
    (Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)).map (action K e)≤
      MulAut.innerSubgroup PSL(3,F) := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  exact map_le_iff_le_comap.mp (maxElementary_action_inner K e hZ hlift hn hF S A hA)

theorem center_le_maxElementary (K:Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e:K ⧸ center K≃*PSL(3,F)) (hZ:IsPGroup 2 (center K))
    [IsElementaryAbelian 2 (center K)]
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W →
      IsElementaryAbelian 2 (W.comap (projection K e)))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G)
    (A:Subgroup G) (hA:A∈Stellmacher.elementaryAbelianMaxSubgroups (S:Subgroup G)) :
    (center K).map K.subtype≤A := by
  let Z:=(center K).map K.subtype
  have hi:=maxElementary_action_inner K e hZ hlift hn hF S A hA
  let : IsElementaryAbelian 2 A:=hA.2.1
  let : IsElementaryAbelian 2 Z:=IsElementaryAbelian.map K.subtype
  obtain ⟨R,hR⟩:=S.exists_subgroupOf_eq_of_normal K
  have hZS : Z≤(S:Subgroup G) := by
    rintro _ ⟨k,hk,rfl⟩
    have hh : k∈(R:Subgroup K):=hZ.le_sylow_of_normal R hk
    rw [hR] at hh
    exact hh
  have hc : Z≤centralizer (A:Set G) := by
    rintro _ ⟨z,hz,rfl⟩ a ha
    obtain ⟨b,hb⟩:=hi (mem_map_of_mem (action K e) ha)
    obtain ⟨k,hk⟩ := (MulAut.centralQuotientAction_inner_iff e
      (MulAut.conjNormal a:MulAut K)).mp ⟨b,hb.symm⟩
    have he : (MulAut.conjNormal a:MulAut K) z=z := by
      rw [hk]
      change k*z*k⁻¹=z
      rw [mem_center_iff.mp hz k,mul_inv_cancel_right]
    have he' := congrArg (fun y:K=>(y:G)) he
    exact mul_inv_eq_iff_eq_mul.mp he'
  have helm : IsElementaryAbelian 2 (A⊔Z:Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hc
  have heq : A=A⊔Z := eq_of_le_of_card_ge le_sup_left
    (hA.2.2 _ (sup_le hA.1 hZS) helm)
  rw [heq]
  exact le_sup_right


theorem sylow_component_le_thompson (K:Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e:K ⧸ center K≃*PSL(3,F)) (hZ:IsPGroup 2 (center K))
    [IsElementaryAbelian 2 (center K)]
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W →
      IsElementaryAbelian 2 (W.comap (projection K e)))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G) :
    (S:Subgroup G)⊓K≤Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) := by
  let : CharP F 2 := by
    let := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by simpa only [←Nat.card_eq_fintype_card] using hF)
  let q:=projection K e
  let f:=action K e
  let J:=Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)
  obtain ⟨R,hR⟩:=S.exists_subgroupOf_eq_of_normal K
  let P:=R.mapSurjective (f:=q) (projection_surjective K e)
  let eU : U F≃*P := (unipotentEquiv F).trans (Sylow.equiv (unipotentSylow F (by omega) hF) P)
  let j:U F→*PSL(3,F):=(P:Subgroup PSL(3,F)).subtype.comp eU.toMonoidHom
  have hj : Function.Injective j:=Subtype.val_injective.comp eU.injective
  have hkerR : q.ker≤(R:Subgroup K) := by
    rw [projection_ker]
    exact hZ.le_sylow_of_normal R
  obtain ⟨A,hA⟩:=Stellmacher.elementaryAbelianMaxSubgroups_nonempty (S:Subgroup G)
  have hZA:=center_le_maxElementary K e hZ hlift hn hF S A hA
  let : IsElementaryAbelian 2 A:=hA.2.1
  let : IsElementaryAbelian 2 (A.map f):=IsElementaryAbelian.map f
  have hi:=maxElementary_action_inner K e hZ hlift hn hF S A hA
  have hq : center PSL(3,F)=⊥ := by
    let := Atlas.sl_perfect (F:=F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
  let eI : PSL(3,F)≃*MulAut.innerSubgroup PSL(3,F) :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hq)
  have hrI : primeRank 2 (MulAut.innerSubgroup PSL(3,F))=2*n :=
    (Theory.GroupTheory.primeRank_equiv 2 eI).symm.trans (Matrix.PSL3Even.two_rank F (by omega) hF)
  have hcA : Nat.card (A.map f)≤(Nat.card F)^2 := by
    let B := (A.map f).subgroupOf (MulAut.innerSubgroup PSL(3,F))
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hi
    have hb := (primeRank_le_iff_elementary_card_le (MulAut.innerSubgroup PSL(3,F))).mp
      hrI.le B inferInstance
    rw [Nat.card_congr (subgroupOfEquivOfLe hi).toEquiv] at hb
    simpa only [hF,←pow_mul,Nat.mul_comm n 2] using hb
  have hfc : f.comp K.subtype=(MulAut.conj : PSL(3,F)→*MulAut PSL(3,F)).comp q := by
    apply MonoidHom.ext
    intro k
    exact action_on_K K e k
  have hplane (V₀:Subgroup (U F)) [IsElementaryAbelian 2 V₀]
      (hv:Nat.card V₀=(Nat.card F)^2) :
      ((V₀.map j).comap q).map K.subtype≤J := by
    let W:=V₀.map j
    let V:=(W.comap q).map K.subtype
    have hWP : W≤(P:Subgroup PSL(3,F)) := by
      rintro _ ⟨u,hu,rfl⟩
      exact (eU u).property
    let : IsElementaryAbelian 2 W:=IsElementaryAbelian.map j
    let : IsElementaryAbelian 2 (W.comap q):=hlift W inferInstance
    let : IsElementaryAbelian 2 V:=IsElementaryAbelian.map K.subtype
    have hVS : V≤(S:Subgroup G) := by
      rintro _ ⟨k,hk,rfl⟩
      have hk' : k∈((R:Subgroup K).map q).comap q := hWP hk
      rw [comap_map_eq_self hkerR,hR] at hk'
      exact hk'
    have hc : V≤centralizer (A⊓f.ker:Set G) := by
      rintro _ ⟨k,hk,rfl⟩ a ha
      have haC : a∈centralizer (K:Set G) := action_ker_eq K e ▸ ha.2
      exact (haC _ k.property).symm
    have hk : V⊓f.ker≤A := by
      rintro _ ⟨⟨k,hk,rfl⟩,hf⟩
      have hc : (k:G)∈centralizer (K:Set G) := action_ker_eq K e ▸ hf
      apply hZA
      refine ⟨k,mem_center_iff.mpr ?_,rfl⟩
      intro y
      exact Subtype.ext (hc y y.property)
    have hVm : V.map f=W.map (MulAut.conj : PSL(3,F)→*MulAut PSL(3,F)) := by
      rw [show V.map f=(W.comap q).map (f.comp K.subtype) from Subgroup.map_map _ _ _,hfc,
        ←Subgroup.map_map,map_comap_eq_self_of_surjective (projection_surjective K e)]
    have hcard : Nat.card (V.map f)=(Nat.card F)^2 := by
      rw [hVm,card_map_of_injective (MulAut.conj_injective_of_center_eq_bot hq),
        show W=V₀.map j from rfl,card_map_of_injective hj,hv]
    exact Stellmacher.elementary_le_maxJ_of_image_bound_of_kernel_le
      (S:Subgroup G) A V f hA hVS hc hk (hcard ▸ hcA)
  let B:=J.comap K.subtype
  have hZB : q.ker≤B := by
    rw [projection_ker]
    intro z hz
    exact (le_sSup hA) (hZA (mem_map_of_mem K.subtype hz))
  have hW (V₀:Subgroup (U F)) [IsElementaryAbelian 2 V₀]
      (hv:Nat.card V₀=(Nat.card F)^2) : V₀.map j≤B.map q := by
    intro w hw
    obtain ⟨k,rfl⟩:=projection_surjective K e w
    exact ⟨k,hplane V₀ hv (mem_map_of_mem K.subtype hw),rfl⟩
  have h1:=hW (V₁ F) (card_V₁ F)
  have h2:=hW (V₂ F) (card_V₂ F)
  have hPB : (P:Subgroup PSL(3,F))≤B.map q := by
    intro x hx
    obtain ⟨u,hu⟩:=eU.surjective ⟨x,hx⟩
    have hju : j u=x:=congrArg Subtype.val hu
    rw [←hju]
    have hu : u=(⟨0,u.y,u.c⟩:U F)*(⟨u.x,0,0⟩:U F) := by
      apply U.ext <;> simp
    rw [hu,map_mul]
    exact (B.map q).mul_mem
      (h2 (mem_map_of_mem j ((mem_V₂ F _).mpr rfl)))
      (h1 (mem_map_of_mem j ((mem_V₁ F _).mpr rfl)))
  intro x hx
  have hk : (⟨x,hx.2⟩:K)∈(R:Subgroup K) := by rw [hR];exact hx.1
  have hqk := hPB (mem_map_of_mem q hk)
  have hh : (⟨x,hx.2⟩:K)∈(B.map q).comap q:=hqk
  rw [comap_map_eq_self hZB] at hh
  exact hh

theorem thompson_le_sylow_component_centralizer
    (K:Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e:K ⧸ center K≃*PSL(3,F)) (hZ:IsPGroup 2 (center K))
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W →
      IsElementaryAbelian 2 (W.comap (projection K e)))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G) :
    Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) ≤
      ((S:Subgroup G)⊓K) ⊔ ((S:Subgroup G)⊓centralizer (K:Set G)) := by
  let f := action K e
  let q := projection K e
  have hi := thompson_action_inner K e hZ hlift hn hF S
  have hJS : Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) ≤ (S:Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hq : center PSL(3,F)=⊥ := by
    let := Atlas.sl_perfect (F:=F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal K
  let R' := R.mapSurjective (f:=q) (projection_surjective K e)
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
    change q k=b at hke
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

/-- The literal Thompson product in the central linear branch of 2.5.7. -/
theorem thompson_eq_sylow_component_sup_centralizer
    (K:Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e:K ⧸ center K≃*PSL(3,F)) (hZ:IsPGroup 2 (center K))
    [IsElementaryAbelian 2 (center K)]
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W →
      IsElementaryAbelian 2 (W.comap (projection K e)))
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) (S:Sylow 2 G) :
    Stellmacher.elementaryAbelianMaxJ (S:Subgroup G) =
      ((S:Subgroup G)⊓K) ⊔
        (Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)⊓centralizer (K:Set G)) := by
  let J:=Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)
  let SK:=(S:Subgroup G)⊓K
  let SC:=(S:Subgroup G)⊓centralizer (K:Set G)
  have hKJ : SK≤J := sylow_component_le_thompson K e hZ hlift hn hF S
  have hnC : SC≤normalizer (SK:Set G) :=
    (inf_le_right.trans (centralizer_le (show SK≤K from inf_le_right))).trans
      (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm ?_ (sup_le hKJ inf_le_left)
  intro x hx
  have hp : x∈(SK:Set G)*(SC:Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left SK SC hnC]
    exact thompson_le_sylow_component_centralizer K e hZ hlift hn hF S hx
  obtain ⟨k,hk,c,hc,hkc⟩ := hp
  have hcJ : c∈J := by
    have hh := J.mul_mem (J.inv_mem (hKJ hk)) hx
    rw [←hkc,inv_mul_cancel_left] at hh
    exact hh
  rw [←hkc]
  exact (SK⊔(J⊓centralizer (K:Set G))).mul_mem
    (mem_sup_left hk) (mem_sup_right ⟨hcJ,hc.2⟩)

end Matrix.PSL3Even.ThompsonCentralCover

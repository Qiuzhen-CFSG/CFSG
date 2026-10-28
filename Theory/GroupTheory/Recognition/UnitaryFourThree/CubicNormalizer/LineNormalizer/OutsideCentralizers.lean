module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.ReflectionFixed
public import Theory.GroupTheory.SylowEightCentralizerBound
public import Theory.GroupTheory.SylowCentralizerConjugacy
/-!
# Outside-reflection centralizers in the global cubic normalizer.
The Sylow center lies in the cubic centralizer, forcing two-part at most4.
The original fixed nine and the commuting four give the full order36.
Source: Aschbacher, Sporadic Groups (1994),45.7(3),printed p.245.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
private theorem divisor_36 (n:ℕ) (hd:n∣1152) (h8:¬8∣n) : n∣36 := by
  have he:Nat.gcd n 128*Nat.gcd n 9=n:=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (by decide:Nat.Coprime 128 9)).mpr hd
  obtain ⟨k,hk,hpow⟩:=(Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.gcd n 128∣2^7 from Nat.gcd_dvd_right _ _)
  have hk2:k≤2:=by
    by_contra hn
    have hh:2^3∣2^k:=pow_dvd_pow 2 (by omega)
    rw[←hpow] at hh
    exact h8 (hh.trans (Nat.gcd_dvd_left _ _))
  have h4:Nat.gcd n 128∣4:=hpow ▸ pow_dvd_pow 2 hk2
  rw[←he]
  exact Nat.mul_dvd_mul h4 (Nat.gcd_dvd_right _ _)


theorem outside_reflection_centralizer_le (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hlocal:centralizer z⊓normalizer
      ((((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)=
      centralizer z⊓normalizer ((P:Subgroup (centralizer z)).map (centralizer z).subtype:Set G))
    (v:G) (hv:v∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hv2:orderOf v=2) (hvS:v∉zpowers z⊔zpowers m.t) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
    normalizer (U:Set G)⊓Subgroup.centralizer ({v}:Set G)≤CubicNormalizer.oddKernel X⊔R.cubicSylow X := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
  let V:=CubicNormalizer.oddKernel X
  let T:=R.cubicSylow X
  let S:=zpowers z⊔zpowers m.t
  let K:=normalizer (U:Set G)
  have hTK:T≤K:=by
    have he:T≤centralizer z⊓K:=by
      rw[hlocal]
      exact le_inf (inf_le_left.trans R.T_le_centralizer) inf_le_right
    exact he.trans inf_le_right
  have hT8:Nat.card T=8:=R.cubicSylow_card h X (h.cubic_sylow_image_card P) (map_subtype_le _)
  let TS:Sylow 2 K:=((IsPGroup.of_card (p:=2) (n:=3) hT8).comap_subtype:IsPGroup 2 (T.subgroupOf K)).toSylow
    (R.cubicSylow_not_dvd_line_index h P m ht hs hlocal)
  have hTSc:Nat.card TS=8:=(Nat.card_congr (subgroupOfEquivOfLe hTK).toEquiv).trans hT8
  let C:=(Subgroup.centralizer (U:Set G)).subgroupOf K
  let : C.Normal:=by
    have he:C=U.normalizerMonoidHom.ker:=U.normalizerMonoidHom_ker.symm
    exact he ▸ U.normalizerMonoidHom.normal_ker
  have hZ:(center TS).map (TS:Subgroup K).subtype≤C:=by
    rintro _ ⟨a,ha,rfl⟩
    have hat:=mem_center_iff.mp ha (⟨⟨m.t,hTK ht⟩,ht⟩:TS)
    have haC:(a:G)∈Subgroup.centralizer ({m.t}:Set G):=mem_centralizer_singleton_iff.mpr
      (congrArg (fun x:TS=>(x:G)) hat).symm
    have heS:T⊓Subgroup.centralizer ({m.t}:Set G)=S:=R.cubicSylow_reflection_centralizer h P m ht hs
    have haS:(a:G)∈S:=heS ▸ ⟨a.property,haC⟩
    have he:T⊓Subgroup.centralizer (U:Set G)=S:=R.reflected_four_eq_sylow_fixed h P m ht hs
    exact ((he.symm ▸ haS): (a:G)∈T⊓Subgroup.centralizer (U:Set G)).2
  let vk:K:=⟨v,hTK hv⟩
  have hvk2:orderOf vk=2:=(orderOf_injective K.subtype K.subtype_injective vk).symm.trans hv2
  have hvC:vk∉C:=by
    intro hh
    exact hvS ((R.reflected_four_eq_sylow_fixed h P m ht hs) ▸ ⟨hv,hh⟩)
  have h8:=not_eight_dvd_centralizer_of_sylow_center_le_normal TS hTSc C hZ vk hvk2 hvC
  let D:=K⊓Subgroup.centralizer ({v}:Set G)
  have hDc:Nat.card (Subgroup.centralizer ({vk}:Set K))=Nat.card D:=by
    rw[←card_map_of_injective K.subtype_injective,map_subtype_centralizer_singleton]
  rw[hDc] at h8
  have hHC:Nat.card (Subgroup.centralizer ({v}:Set G))=1152:=by
    obtain ⟨g,hg⟩:=isConj_iff.mp (h.involution_fused v hv2)
    have he:=(⊤:Subgroup G).card_inf_centralizer_conj g
      (mem_normalizer_iff.mpr (fun _=>by simp):g∈normalizer (⊤:Subgroup G)) z
    simp only[top_inf_eq,hg] at he
    rw[←he]
    exact h.centralizer_card
  have hd:Nat.card D∣1152:=hHC ▸ card_dvd_of_le (show D≤Subgroup.centralizer ({v}:Set G) from inf_le_right)
  have h36:Nat.card D∣36:=divisor_36 _ hd h8
  let E:=zpowers z⊔zpowers v
  let F:=V⊓Subgroup.centralizer ({v}:Set G)
  have hzT:z∈T:=by
    have he:=R.cubicSylow_inf_core h X (h.cubic_sylow_image_card P) (map_subtype_le _)
    exact ((he.symm ▸ mem_zpowers z):z∈core z⊓R.cubicSylow X).2
  have hET:E≤T:=sup_le (zpowers_le.mpr hzT) (zpowers_le.mpr hv)
  have hzv:Commute z v:=(mem_centralizer_singleton_iff.mp (R.T_le_centralizer hv.1)).symm
  have hE4:Nat.card E=4:=by
    have hvZ:v∉zpowers z:=fun hh=>hvS (mem_sup_left hh)
    have hvN:v∈normalizer (zpowers z:Set G):=(centralizer_le_normalizer _)
      (fun x hx=>by obtain ⟨k,rfl⟩:=mem_zpowers_iff.mp hx;exact (hzv.zpow_left k).eq)
    rw[card_sup_zpowers_of_normalizing_involution (zpowers z) v (hv2 ▸ pow_orderOf_eq_one v) hvZ hvN,
      Nat.card_zpowers,h.involution]
  have hF9:Nat.card F=9:=R.outside_reflection_kernel_fixed_card h P m ht hs v hv hv2 hvS
  have hEF:E≤normalizer (F:Set G):=by
    apply (le_inf (hET.trans (inf_le_right.trans (CubicNormalizer.normalizer_normalizes_oddKernel X))) ?_).trans
      inf_normalizer_le_normalizer_inf
    exact (sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzv.eq))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))).trans le_normalizer
  have hdis:F⊓E=⊥:=(disjoint_of_coprime_natCard (by rw[hF9,hE4];decide)).eq_bot
  have hprod:Nat.card (E⊔F:Subgroup G)=36:=by
    have hh:=card_mul_eq_card_inf_mul_card_sup_of_normalizes F E hEF
    rw[hF9,hE4,hdis,card_bot,one_mul] at hh
    rw[sup_comm,←hh]
  let : IsElementaryAbelian 3 V:=(h.reflected_kernel_of_source_binary_normalizers P m).1
  have hXV:X≤V:=by rw[←h.toCentralizerHypothesis.cubic_oddKernel_fixed X (h.cubic_sylow_image_card P) (map_subtype_le _)];exact inf_le_left
  have hVK:V≤K:=(show V≤Subgroup.centralizer (U:Set G) from fun a ha u hu=>
    congrArg Subtype.val (mul_comm' (⟨u,hXV hu.1⟩:V) (⟨a,ha⟩:V))).trans (centralizer_le_normalizer _)
  have hED:E⊔F≤D:=sup_le
    (le_inf (hET.trans hTK) (sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzv.eq))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))))
    (le_inf (inf_le_left.trans hVK) inf_le_right)
  have he:E⊔F=D:=eq_of_le_of_card_ge hED (by rw[hprod];exact Nat.le_of_dvd (by decide) h36)
  change D≤V⊔T
  rw[←he]
  exact sup_le (hET.trans le_sup_right) (inf_le_left.trans le_sup_left)
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair

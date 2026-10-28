module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.Four
/-!
# The original involution fixed nines

The fixed four is the reflection centralizer in the original eight. An
outside involution is conjugated to its product with z by t. Its original
nine fixed line and the order81 kernel force a fixed nine. The three
nonidentity actors in the fixed four likewise have fixed nines.
Source: Aschbacher, Sporadic Groups (1994),45.7(3),printed p.245.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
omit [Finite G] in
private theorem two_line_cases (hz2:orderOf z=2) {x:G} (hx:x∈zpowers z) : x=1∨x=z := by
  obtain ⟨a,ha,huniq⟩:=(Nat.card_eq_two_iff' (1:zpowers z)).mp (by rw[Nat.card_zpowers,hz2])
  by_cases hx1:x=1
  · exact Or.inl hx1
  right
  have hz:z≠1:=by intro he;have hh:=hz2;simp[he] at hh
  exact congrArg Subtype.val ((huniq ⟨x,hx⟩ (fun he=>hx1 (congrArg Subtype.val he))).trans
    (huniq ⟨z,mem_zpowers z⟩ (fun he=>hz (congrArg Subtype.val he))).symm)

theorem cubicSylow_reflection_centralizer (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) :
    R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓Subgroup.centralizer ({m.t}:Set G)=
      zpowers z⊔zpowers m.t := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let T:=R.cubicSylow X
  let S:=zpowers z⊔zpowers m.t
  have hzT:z∈T:=by
    have hh:=R.cubicSylow_inf_core h X (h.cubic_sylow_image_card P) (map_subtype_le _)
    exact ((hh.symm ▸ mem_zpowers z):z∈core z⊓R.cubicSylow X).2
  have hle:S≤T⊓Subgroup.centralizer ({m.t}:Set G):=sup_le
    (zpowers_le.mpr ⟨hzT,mem_centralizer_singleton_iff.mpr m.zt_commute.eq⟩)
    (zpowers_le.mpr ⟨ht,mem_centralizer_singleton_iff.mpr rfl⟩)
  have hsC:m.s∉Subgroup.centralizer ({m.t}:Set G):=by
    intro hh
    have he:m.s*m.t*m.s⁻¹=m.t:=mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hh)
    have hz:z=1:=mul_left_cancel (show m.t*z=m.t*1 by simpa only[mul_one] using m.reflection_conjugation.symm.trans he)
    have hh:=h.involution
    simp [hz] at hh
  have hcard:Nat.card T=8:=R.cubicSylow_card h X (h.cubic_sylow_image_card P) (map_subtype_le _)
  have hd:Nat.card (T⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G)∣8:=hcard ▸ card_dvd_of_le inf_le_left
  have hge:4≤Nat.card (T⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):=by
    rw [←(h.reflected_four P m).2];exact card_le_of_le hle
  have hne:Nat.card (T⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G)≠8:=by
    intro hh
    have he:T⊓Subgroup.centralizer ({m.t}:Set G)=T:=eq_of_le_of_card_ge inf_le_left (by rw [hh,hcard])
    exact hsC ((he.symm ▸ (show m.s∈T from hs)).2)
  have hc:Nat.card (T⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G)=4:=by
    have hh:=Nat.mem_divisors.mpr ⟨hd,(by decide:8≠0)⟩
    have he:Nat.divisors 8={1,2,4,8}:=by decide
    simp only [he,Finset.mem_insert,Finset.mem_singleton] at hh
    omega
  exact (eq_of_le_of_card_ge hle (by rw [hc,(h.reflected_four P m).2])).symm

theorem outside_reflection_conjugation (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (v:G) (hv:v∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hv2:v^2=1) (hvS:v∉zpowers z⊔zpowers m.t) : m.t*v*m.t⁻¹=v*z := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  have hnot:¬Commute m.t v := by
    intro hc
    exact hvS ((R.cubicSylow_reflection_centralizer h P m ht hs) ▸
      (show v∈R.cubicSylow X⊓Subgroup.centralizer ({m.t}:Set G) from
        ⟨hv,mem_centralizer_singleton_iff.mpr hc.symm.eq⟩))
  have ht2:m.t^2=1:=m.t_order ▸ pow_orderOf_eq_one m.t
  have hti:m.t⁻¹=m.t:=inv_eq_of_mul_eq_one_left (by simpa only[pow_two] using ht2)
  have hvi:v⁻¹=v:=inv_eq_of_mul_eq_one_left (by simpa only[pow_two] using hv2)
  have hp:(m.t*v)^2∈zpowers z:=R.cubicSylow_square_mem_line h X (h.cubic_sylow_image_card P)
    (map_subtype_le _) _ ((R.cubicSylow X).mul_mem ht hv)
  have hpne:(m.t*v)^2≠1:=by
    intro he
    have hi:(m.t*v)⁻¹=m.t*v:=inv_eq_of_mul_eq_one_left (by simpa only[pow_two] using he)
    apply hnot
    change m.t*v=v*m.t
    simpa only[mul_inv_rev,hti,hvi] using hi.symm
  have hpz:(m.t*v)^2=z:=(two_line_cases h.involution hp).resolve_left hpne
  calc
    m.t*v*m.t⁻¹=(m.t*v)^2*v⁻¹ := by rw[hti];simp only[pow_two];group
    _=z*v := by rw[hpz,hvi]
    _=v*z := (mem_centralizer_singleton_iff.mp (R.T_le_centralizer hv.1)).symm

theorem outside_reflection_kernel_fixed_card (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (v:G) (hv:v∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hv2:orderOf v=2) (hvS:v∉zpowers z⊔zpowers m.t) :
    Nat.card (CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓
      Subgroup.centralizer ({v}:Set G):Subgroup G)=9 := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  have hvQ:v∉core z:=by
    intro hh
    have hvZ:v∈zpowers z:=(R.cubicSylow_inf_core h X (h.cubic_sylow_image_card P) (map_subtype_le _)) ▸ ⟨hh,hv⟩
    exact hvS (mem_sup_left hvZ)
  have hp:v^2=1:=hv2 ▸ pow_orderOf_eq_one v
  have hf:=R.cubic_involution_fixed_card h X (h.cubic_sylow_image_card P) (map_subtype_le _) v hv hp hvQ
  have hc:=h.cubic_oddKernel_reflection_count X (h.cubic_sylow_image_card P) (map_subtype_le _)
    v m.t hv2 hv.2 (mem_centralizer_singleton_iff.mp (R.T_le_centralizer hv.1)).symm
    (h.involution_fused v hv2) ht.2 (R.outside_reflection_conjugation h P m ht hs v hv hp hvS) hf
  have h81:Nat.card (CubicNormalizer.oddKernel X)=81:=(h.reflected_kernel_of_source_binary_normalizers P m).2
  dsimp only at hc
  rw [h81] at hc
  rcases hc.1 with h3|h9
  · rw[h3] at hc
    norm_num at hc
  · exact h9

omit [Finite G] in
theorem reflected_four_cases (h:IsType z) {X:Subgroup G}
    (m:CubicNormalizer.ReflectedMarking z X) {v:G} (hv:v∈zpowers z⊔zpowers m.t) :
    v=1∨v=z∨v=m.t∨v=z*m.t := by
  have hnorm:zpowers m.t≤normalizer (zpowers z:Set G):=zpowers_le.mpr
    ((centralizer_le_normalizer _) (fun x hx=>by
      obtain ⟨k,rfl⟩:=mem_zpowers_iff.mp hx
      exact (m.zt_commute.zpow_left k).eq))
  have hvp:v∈(zpowers z:Set G)*(zpowers m.t:Set G):=by
    rw[←coe_mul_of_right_le_normalizer_left (zpowers z) (zpowers m.t) hnorm]
    exact hv
  obtain ⟨a,ha,b,hb,rfl⟩:=hvp
  rcases two_line_cases h.involution ha with rfl|rfl <;>
    rcases two_line_cases m.t_order hb with rfl|rfl <;> simp

theorem reflected_four_kernel_fixed_card (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (v:G) (hv:v∈zpowers z⊔zpowers m.t) (hv1:v≠1) :
    Nat.card (CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓
      Subgroup.centralizer ({v}:Set G):Subgroup G)=9 := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  have hX:Nat.card X=9:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  have hF:Nat.card (V⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G)=9:=by
    have hc:=h.cubic_oddKernel_reflection_count X hX hXH m.t m.s m.t_order m.t_normalizes
      m.zt_commute m.t_fused m.s_normalizes m.reflection_conjugation m.common_fixed_card
    have h81:Nat.card V=81:=(h.reflected_kernel_of_source_binary_normalizers P m).2
    dsimp only at hc
    rw[h81] at hc
    rcases hc.1 with h3|h9
    · rw[h3] at hc;norm_num at hc
    · exact h9
  rcases reflected_four_cases h m hv with rfl|rfl|rfl|rfl
  · exact (hv1 rfl).elim
  · change Nat.card (CubicNormalizer.oddKernel X⊓centralizer _:Subgroup G)=9
    rw[h.toCentralizerHypothesis.cubic_oddKernel_fixed X hX hXH,hX]
  · exact hF
  · have he:=V.card_inf_centralizer_conj m.s (CubicNormalizer.normalizer_normalizes_oddKernel X m.s_normalizes) m.t
    rw[m.reflection_conjugation,←m.zt_commute.eq] at he
    exact he.symm.trans hF
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair

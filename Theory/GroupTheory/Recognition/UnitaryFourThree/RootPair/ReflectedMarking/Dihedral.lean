module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ReflectedMarking.Placement
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.OutsideFusion
/-!
# The original cubic reflections and their dihedral relation

The source plane cosets supply two independent involutions in Tx=T∩N(X).
The original outside-root fusion puts every involution outside Q in R.
If Tx were elementary, its intrinsic UT3 realization would put it inside
one plane, contradicting T=Q Tx and the plane-core product order64.
The two lifted reflections therefore do not commute. Every square in Tx
lies in the marked line, so their product squares to z, giving the literal
dihedral conjugation relation. All hypotheses are the original IsType data.

Source: Aschbacher, Sporadic Groups,45.3(5) and45.5(4), pp.243–244.
-/
@[expose] public section
open Subgroup
open Theory.GroupTheory.HyperbolicRecognition
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z:G}
namespace RootPair
variable (P:RootPair z)

theorem elementary_in_R_le_plane (h:IsType z) (U:Subgroup G)
    [IsElementaryAbelian 2 U] (hUR:U≤P.R) :
    ∃V:Subgroup G,U≤V ∧ V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16 := by
  obtain ⟨e⟩:=P.nonempty_rootEquiv h
  let U':=U.subgroupOf P.R
  let := IsElementaryAbelian.subgroupOf (p:=2) hUR
  let W:=U'.map e.toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  have transport (V:Subgroup Matrix.PSL3Four.RootNormalizerModel.Root) [IsElementaryAbelian 2 V]
      (hc:Nat.card V=16) (hle:W≤V) :
      ∃V:Subgroup G,U≤V ∧ V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16 := by
    let V':=V.map e.symm.toMonoidHom
    let V₀:=V'.map P.R.subtype
    have hU' : U'≤V' := by
      intro u hu
      exact mem_map.mpr ⟨e u,hle (mem_map_of_mem e.toMonoidHom hu),e.symm_apply_apply u⟩
    have hUV:U≤V₀ := by
      have hh:=map_mono hU' (f:=P.R.subtype)
      rwa [map_subgroupOf_eq_of_le hUR] at hh
    let : IsElementaryAbelian 2 V' := IsElementaryAbelian.map e.symm.toMonoidHom
    refine ⟨V₀,hUV,(map_subtype_le _).trans le_sup_left,IsElementaryAbelian.map P.R.subtype,?_⟩
    rw [card_map_of_injective P.R.subtype_injective,card_map_of_injective e.symm.injective,hc]
  rcases elementary_le_rootPlane W with hW | hW
  · exact transport rootPlane₁ card_rootPlane₁ hW
  · exact transport rootPlane₂ card_rootPlane₂ hW

theorem core_sup_plane_card (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    Nat.card (core z⊔V:Subgroup G)=64 := by
  have hn:V≤normalizer (core z:Set G) :=
    hV.1.trans (P.T_le_centralizer.trans CentralizerHypothesis.centralizer_normalizes_core)
  have hc:=card_mul_eq_card_inf_mul_card_sup_of_normalizes (core z) V hn
  rw [h.toCentralizerHypothesis.core_card,hV.2.2,inf_comm,P.plane_inf_core_card h V hV] at hc
  omega

theorem cubicSylow_not_elementary (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) : ¬IsElementaryAbelian 2 (P.cubicSylow X) := by
  intro he
  let := he
  have hUR:P.cubicSylow X≤P.R := by
    intro u hu
    have hu2:u^2=1 := elemPow_eq_one_of_isElementaryAbelian u hu
    by_cases hu1:u=1
    · rw [hu1]; exact P.R.one_mem
    rcases P.involution_mem_R_or_core h u hu.1 (orderOf_eq_prime hu2 hu1) with huR | huQ
    · exact huR
    · have huZ:u∈zpowers z := (P.cubicSylow_inf_core h X hX hXH) ▸ ⟨huQ,hu⟩
      exact P.E_le_R h (mem_sup_left huZ)
  obtain ⟨V,hUV,hVT,hVE,hVc⟩:=P.elementary_in_R_le_plane h (P.cubicSylow X) hUR
  have hT:P.T≤core z⊔V := by
    rw [P.T_eq_core_sup_cubicSylow h X hX hXH]
    exact sup_le_sup_left hUV _
  have hc:=card_le_of_le hT
  rw [P.T_card h,P.core_sup_plane_card h V ⟨hVT,hVE,hVc⟩] at hc
  omega

theorem exists_cubic_reflection_pair (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) :
    ∃t∈P.cubicSylow X,∃s∈P.cubicSylow X,
      t^2=1 ∧ s^2=1 ∧ t∉core z ∧ s∉core z⊔zpowers t := by
  obtain ⟨d⟩:=P.exists_planePair h
  have hV:d.first≤P.T ∧ IsElementaryAbelian 2 d.first ∧ Nat.card d.first=16 :=
    ⟨d.first_le.trans le_sup_left,d.first_elementary,d.first_card⟩
  have hW:d.second≤P.T ∧ IsElementaryAbelian 2 d.second ∧ Nat.card d.second=16 :=
    ⟨d.second_le.trans le_sup_left,d.second_elementary,d.second_card⟩
  have hVn:¬d.first≤core z := by
    intro hh
    have hc:=P.plane_inf_core_card h d.first hV
    rw [inf_eq_left.mpr hh,d.first_card] at hc
    omega
  obtain ⟨r,hr,hrQ⟩:=SetLike.not_le_iff_exists.mp hVn
  have hWn:¬d.second≤core z⊔d.first := by
    intro hh
    have hRT:P.R≤core z⊔d.first := d.sup_eq ▸ sup_le le_sup_right hh
    have hTT:P.T≤core z⊔d.first := sup_le hRT le_sup_left
    have hc:=card_le_of_le hTT
    rw [P.T_card h,P.core_sup_plane_card h d.first hV] at hc
    omega
  obtain ⟨r',hr',hr'D⟩:=SetLike.not_le_iff_exists.mp hWn
  have hr'Q:r'∉core z := fun hh=>hr'D (mem_sup_left hh)
  obtain ⟨t,ht,ht2,htQ,hrt⟩:=P.cubic_reflection_in_plane_coset h X hX hXH d.first hV r hr hrQ
  obtain ⟨s,hs,hs2,hsQ,hrs⟩:=P.cubic_reflection_in_plane_coset h X hX hXH d.second hW r' hr' hr'Q
  have htD:t∈core z⊔d.first := by
    have hh: r*(r⁻¹*t)∈core z⊔d.first := (core z⊔d.first).mul_mem (mem_sup_right hr) (mem_sup_left hrt)
    simpa only [mul_inv_cancel_left] using hh
  have hsD:s∉core z⊔d.first := by
    intro hh
    have he:r'=s*(r'⁻¹*s)⁻¹ := by group
    rw [he] at hr'D
    exact hr'D ((core z⊔d.first).mul_mem hh ((core z⊔d.first).inv_mem (mem_sup_left hrs)))
  exact ⟨t,ht,s,hs,ht2,hs2,htQ,fun hh=>hsD ((sup_le le_sup_left (zpowers_le.mpr htD)) hh)⟩


theorem cubicSylow_square_mem_line (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) (u:G) (hu:u∈P.cubicSylow X) :
    u^2∈zpowers z := by
  have hp:IsPGroup 2 (P.cubicSylow X) := IsPGroup.of_card (n:=3) (P.cubicSylow_card h X hX hXH)
  have hle:P.cubicSylow X⊓residual z≤core z := h.toCentralizerHypothesis.two_subgroup_le_core
    _ hp.to_inf_left inf_le_right
  have huR:u^2∈residual z := P.centralizer_square_mem_residual h u (P.T_le_centralizer hu.1)
  exact (h.core_cubic_normalizer_intersection X hX hXH) ▸
    (show u^2∈core z⊓normalizer (X:Set G) from ⟨hle ⟨pow_mem hu 2,huR⟩,pow_mem hu.2 2⟩)

theorem cubic_reflection_pair_not_commute (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z)
    (t s:G) (ht:t∈P.cubicSylow X) (hs:s∈P.cubicSylow X)
    (ht2:t^2=1) (hs2:s^2=1) (htQ:t∉core z) (hsQ:s∉core z⊔zpowers t) :
    ¬Commute s t := by
  intro hst
  let Z:=zpowers z
  let K:=Z⊔zpowers t
  have hz2:z^2=1 := h.involution ▸ pow_orderOf_eq_one z
  have hzU:Z≤P.cubicSylow X := by
    change zpowers z≤P.cubicSylow X
    rw [←P.cubicSylow_inf_core h X hX hXH]
    exact inf_le_right
  have hzt:Commute z t := (mem_centralizer_singleton_iff.mp (P.T_le_centralizer ht.1)).symm
  have hzs:Commute z s := (mem_centralizer_singleton_iff.mp (P.T_le_centralizer hs.1)).symm
  have htZ:t∉Z := fun hh=>htQ (h.toCentralizerHypothesis.line_le_core hh)
  have hKn: t∈normalizer (Z:Set G) := (centralizer_le_normalizer _) (fun x hx=>by
    obtain ⟨k,rfl⟩:=mem_zpowers_iff.mp hx
    exact hzt.zpow_left k)
  have hKcard:Nat.card K=4 := by
    rw [card_sup_zpowers_of_normalizing_involution Z t ht2 htZ hKn,Nat.card_zpowers,h.involution]
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  have htC:zpowers t≤Subgroup.centralizer (Z:Set G) := zpowers_le.mpr (fun x hx=>by
    obtain ⟨k,rfl⟩:=mem_zpowers_iff.mp hx
    exact hzt.zpow_left k)
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.sup_of_le_centralizer htC
  have hsK:s∉K := fun hh=>hsQ ((sup_le_sup_right h.toCentralizerHypothesis.line_le_core (zpowers t)) hh)
  have hKs:K≤centralizer s := sup_le
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzs.eq))
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hst.symm.eq))
  have hsKC:s∈Subgroup.centralizer (K:Set G) := fun k hk=>mem_centralizer_singleton_iff.mp (hKs hk)
  let W:=K⊔zpowers s
  have hWcard:Nat.card W=8 := by
    rw [card_sup_zpowers_of_normalizing_involution K s hs2 hsK ((centralizer_le_normalizer _) hsKC),hKcard]
  let : IsElementaryAbelian 2 (zpowers s) := IsElementaryAbelian.zpowers_of_pow_eq_one hs2
  have hW:IsElementaryAbelian 2 W := IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hsKC)
  have hWU:W≤P.cubicSylow X := sup_le (sup_le hzU (zpowers_le.mpr ht)) (zpowers_le.mpr hs)
  have he:W=P.cubicSylow X := eq_of_le_of_card_ge hWU (by rw [hWcard,P.cubicSylow_card h X hX hXH])
  exact P.cubicSylow_not_elementary h X hX hXH (he ▸ hW)

theorem exists_cubic_reflection_relations (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) :
    ∃t∈P.cubicSylow X,∃s∈P.cubicSylow X,
      orderOf t=2 ∧ orderOf s=2 ∧ t∉core z ∧ s∉core z ∧ s*t*s⁻¹=t*z := by
  obtain ⟨t,ht,s,hs,ht2,hs2,htQ,hsQ⟩:=P.exists_cubic_reflection_pair h X hX hXH
  have htc:t≠1 := fun he=>htQ (he ▸ (core z).one_mem)
  have hsc:s≠1 := fun he=>hsQ (he ▸ (core z⊔zpowers t).one_mem)
  have hsQ':s∉core z := fun hh=>hsQ (mem_sup_left hh)
  have hst:=P.cubic_reflection_pair_not_commute h X hX hXH t s ht hs ht2 hs2 htQ hsQ
  have hsi:s⁻¹=s := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs2)
  have hti:t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
  have hpne:(s*t)^2≠1 := by
    intro hp
    have hi:(s*t)⁻¹=s*t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hp)
    apply hst
    change s*t=t*s
    simpa only [mul_inv_rev,hsi,hti] using hi.symm
  have hpZ:(s*t)^2∈zpowers z := P.cubicSylow_square_mem_line h X hX hXH _
    ((P.cubicSylow X).mul_mem hs ht)
  have hzne:z≠1 := by intro he; have hh:=h.involution; simp [he] at hh
  have hpz:(s*t)^2=z := by
    obtain ⟨a,ha,huniq⟩:=(Nat.card_eq_two_iff' (1:zpowers z)).mp (by rw [Nat.card_zpowers,h.involution])
    exact congrArg Subtype.val ((huniq ⟨(s*t)^2,hpZ⟩ (fun he=>hpne (congrArg Subtype.val he))).trans
      (huniq ⟨z,mem_zpowers z⟩ (fun he=>hzne (congrArg Subtype.val he))).symm)
  refine ⟨t,ht,s,hs,orderOf_eq_prime ht2 htc,orderOf_eq_prime hs2 hsc,htQ,hsQ',?_⟩
  calc
    s*t*s⁻¹ = (s*t)^2*t⁻¹ := by rw [hsi]; simp only [pow_two]; group
    _ = z*t := by rw [hpz,hti]
    _ = t*z := (mem_centralizer_singleton_iff.mp (P.T_le_centralizer ht.1)).symm
end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree

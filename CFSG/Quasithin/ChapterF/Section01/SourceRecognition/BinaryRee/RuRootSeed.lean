module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuResidualClass
public import Theory.GroupAction.Order512FiveOrbit
public import Theory.GroupTheory.CommutatorOrbitCard

/-!
# The original fixed root and generating five-orbit

The cyclic subgroup C_{Q₀Q₅}(B₅) has order four. A generator t lies
outside Q₅, belongs to Q₀, and squares to the original central involution.
J.2.4 gives C_{Q₅}(t)=U; normal-subgroup intersection with Z and orbit
counting for B₅ then give [Q₅,t]=U. The original Dα supplies an involution
outside U. Parrott's theorem makes its literal B₅ orbit generate Q₅.
Thus the actual root and orbit generate Q₀Q₅; no frame is assumed.

Source: Aschbacher–Smith J.2.4, J.4.1(3),(6), J.4.5(3),
printed pp.434,440,442; Parrott (1972), pp.672–674.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices Fusion
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)
  (B5 : Sylow 5 d.toTypeRuSetup.H)

theorem firstCore_inf_CQ_card : Nat.card (fiveHyperplane d B5⊓CQ B5:Subgroup G)=4 := by
  have hj : fiveHyperplane d B5⊔CQ B5=d.toTypeRuSetup.Q := by
    apply le_antisymm (sup_le (fiveHyperplane_le_Q d B5) inf_le_left)
    conv_lhs => rw [Q_eq_Q₅_sup_CQ d B5]
    exact sup_le_sup_right (show Q₅ d B5≤fiveHyperplane d B5 from le_sup_right) _
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (fiveHyperplane d B5)
    (CQ B5) ((show CQ B5≤d.toTypeRuSetup.Q from inf_le_left).trans
      (Q_normalizes_fiveHyperplane d B5))
  rw [hj,fiveHyperplane_card,five_centralizer_card,d.ru2.card_Q d.card_Z] at hc
  omega

/-- Choose the original cyclic fixed root and its central square. -/
theorem exists_firstCore_fixed_root : ∃t:G,
    t∈fiveHyperplane d B5 ∧ t∈centralizer (B5Image B5:Set G) ∧
    t∉Q₅ d B5 ∧ orderOf t=4 ∧ t^2∈d.toTypeRuSetup.Z ∧
    zpowers (t^2)=d.toTypeRuSetup.Z ∧
    zpowers t=fiveHyperplane d B5⊓centralizer (B5Image B5:Set G) ∧
    t∈Q₀ d := by
  let C:=fiveHyperplane d B5⊓CQ B5
  have hnot : ¬C≤d.toTypeRuSetup.U := by
    intro h
    have hc : C≤d.toTypeRuSetup.Z := by
      rw [←five_centralizer_inf_U B5]
      exact le_inf inf_le_right h
    have hh := card_le_of_le hc
    rw [firstCore_inf_CQ_card,d.card_Z] at hh
    omega
  obtain ⟨t,ht,htU⟩ := Set.not_subset.mp hnot
  have ht4pow : t^4=1 := congrArg (fun a:fiveHyperplane d B5=>(a:G))
    (firstCore_fourth_power d B5 ⟨t,ht.1⟩)
  have ht2 : t^2≠1 := by
    intro h
    obtain ⟨c⟩ := SourceCompletion.exists_choices d
    have hOmega := (SourceCompletion.fusion c).2.2.1.2.2.2.1
    exact htU ((omegaOneAmbient_le_iff _ _).mp hOmega.le t
      (five_centralizer_le_HC B5 ht.2) h)
  have ho : orderOf t=4 := by
    have hd := orderOf_dvd_of_pow_eq_one ht4pow
    have hn : ¬orderOf t∣2 := fun h => ht2 (orderOf_dvd_iff_pow_eq_one.mp h)
    obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show orderOf t∣2^2 from hd)
    have hk2 : k=2 := by
      by_contra h
      have hk1 : k≤1 := by omega
      apply hn
      rw [he]
      exact (pow_dvd_pow 2 hk1)
    simpa only [hk2,Nat.reducePow] using he
  have htZ : t^2∈d.toTypeRuSetup.Z := by
    rw [←five_centralizer_inf_U B5]
    exact ⟨(CQ B5).pow_mem ht.2 2,firstCore_square_mem_U d B5 ⟨t,ht.1⟩⟩
  have hroot : zpowers t=fiveHyperplane d B5⊓centralizer (B5Image B5:Set G) := by
    have he : fiveHyperplane d B5⊓centralizer (B5Image B5:Set G)=C := by
      dsimp only [C,CQ]
      rw [←inf_assoc,inf_eq_left.mpr (fiveHyperplane_le_Q d B5)]
    rw [he]
    apply eq_of_le_of_card_ge (zpowers_le.mpr ht)
    rw [Nat.card_zpowers,ho,firstCore_inf_CQ_card]
  refine ⟨t,ht.1,ht.2.2,?_,ho,htZ,?_,hroot,?_⟩
  · intro hp
    exact htU (d.ru2.natural.kernel_le ((Q₅_inf_CQ d B5).le ⟨hp,ht.2⟩))
  · apply eq_of_le_of_card_ge (zpowers_le.mpr htZ)
    rw [Nat.card_zpowers,orderOf_pow,ho,d.card_Z]
    decide
  · exact (firstCore_inf_HC d B5).le ⟨ht.1,five_centralizer_le_HC B5 ht.2⟩

/-- Every original five-orbit outside U generates Q₅. -/
theorem Q₅_five_orbit_generates (b:Q₅ d B5) (hb:(b:G)∉d.toTypeRuSetup.U) :
    closure (Set.range (fun a:B5Image B5=>(a:G)*(b:G)*(a:G)⁻¹))=Q₅ d B5 := by
  let P:=Q₅ d B5
  let A:=B5Image B5
  let : MulDistribMulAction A P := conjMulDistribMulActionOfLeNormalizer A P
    (normalizer_commutator_ge_right _ _)
  have hfix : FixedPoints.subgroup A P≤center P := by
    intro x hx
    have hxc : (x:G)∈CQ B5 := by
      refine ⟨Q₅_le_Q d B5 x.property,?_⟩
      intro a ha
      have he := congrArg (fun y:P=>(y:G)) (hx ⟨a,ha⟩)
      change a*(x:G)*a⁻¹=(x:G) at he
      exact mul_inv_eq_iff_eq_mul.mp he
    have hxZ := (Q₅_inf_CQ d B5).le ⟨x.property,hxc⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact ((pCoreIn_le 2 _ (Q₅_le_Q d B5 y.property)) (x:G) hxZ).symm
  have hbD : b∉_root_.commutator P := by
    intro h
    apply hb
    rw [←Q₅_derived_eq_U d B5,←map_subtype_commutator]
    exact mem_map_of_mem P.subtype h
  have hgen := Theory.GroupAction.parrott_orbit_closure_eq_top
    ((isPGroup_pCoreIn 2 d.toTypeRuSetup.H).of_injective
      (inclusion (Q₅_le_Q d B5)) (inclusion_injective _))
    (card_Q₅ d B5) (Q₅_class_at_least_three d B5) (B5Image_card d.card_Z B5) hfix b hbD
  have hm := congrArg (Subgroup.map P.subtype) hgen
  rw [MonoidHom.map_closure,←Set.range_comp,←MonoidHom.range_eq_map,range_subtype] at hm
  exact hm

/-- Every nontrivial normal subgroup of the actual residual contains Z. -/
theorem Q₅_normal_contains_Z (N:Subgroup G) (hN:N≤Q₅ d B5)
    (hn:Q₅ d B5≤normalizer N) (hc:1<Nat.card N) : d.toTypeRuSetup.Z≤N := by
  let P:=Q₅ d B5
  let D:=N.subgroupOf P
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 P) := ⟨IsPGroup.of_card (n:=9) (card_Q₅ d B5)⟩
  let : D.Normal := normal_subgroupOf_of_le_normalizer hn
  have hd : Nat.card D=Nat.card N := Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv
  let : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (hd.symm ▸ hc)
  obtain ⟨w,hw,hwZ⟩ := exists_nontrivial_center_mem_normal D (p:=2)
  have hZ : ((w:P):G)∈d.toTypeRuSetup.Z := by
    rw [←Q₅_center_eq_Z d B5]
    exact mem_map_of_mem P.subtype hwZ
  have hnG : ((w:P):G)≠1 := by
    intro h
    exact hw (Subtype.ext (Subtype.ext h))
  have hzpow : zpowers ((w:P):G)=d.toTypeRuSetup.Z := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hZ)
    rw [d.card_Z]
    exact Nat.succ_le_of_lt ((one_lt_card_iff_ne_bot _).mpr (by
      intro h
      exact hnG (h.le (mem_zpowers ((w:P):G)))))
  rw [←hzpow]
  exact zpowers_le.mpr w.property

/-- The fixed root supplements the actual residual in the first core. -/
theorem Q₅_sup_fixed_root (t:G) (ht:t∈fiveHyperplane d B5) (hn:t∉Q₅ d B5) :
    Q₅ d B5⊔zpowers t=fiveHyperplane d B5 := by
  let P:=Q₅ d B5
  let N:=P⊔zpowers t
  have hN : N≤fiveHyperplane d B5 := sup_le le_sup_right (zpowers_le.mpr ht)
  have hlarge : 512<Nat.card N := by
    by_contra hh
    have he : P=N := eq_of_le_of_card_ge le_sup_left (by rw [card_Q₅]; omega)
    exact hn (he.ge (show t∈N from (show zpowers t≤N from le_sup_right) (mem_zpowers t)))
  obtain ⟨k,hk⟩ := card_dvd_of_le (show P≤N from le_sup_left)
  change Nat.card N=Nat.card P*k at hk
  rw [card_Q₅] at hk
  apply eq_of_le_of_card_ge hN
  rw [fiveHyperplane_card]
  omega

/-- J.2.4 identifies the root centralizer inside the residual. -/
theorem Q₅_fixed_root_centralizer (t:G) (ht:t∈Q₀ d) (hn:t∉Q₅ d B5) :
    Q₅ d B5⊓centralizer ({t}:Set G)=d.toTypeRuSetup.U := by
  have htC:=Q₀_le_HC d ht
  have htU:t∉d.toTypeRuSetup.U := fun h=>hn (U_le_Q₅ d B5 h)
  apply le_antisymm
  · intro x hx
    have hcomm : ⁅t,x⁆∈d.toTypeRuSetup.Z := by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_singleton_iff.mp hx.2).symm]
      exact d.toTypeRuSetup.Z.one_mem
    exact (Q₅_inf_HC d B5).le ⟨hx.1,(HC_commutator_mem_Z_iff d t htC htU
      ⟨x,Q₅_le_Q d B5 hx.1⟩).mp hcomm⟩
  · intro x hx
    exact ⟨U_le_Q₅ d B5 hx,mem_centralizer_singleton_iff.mpr (htC.2 x hx)⟩

/-- Its commutators with Q₅ fill U, before taking any quotient. -/
theorem Q₅_fixed_root_commutator (t:G) (ht:t∈Q₀ d) (hn:t∉Q₅ d B5)
    (hf:t∈centralizer (B5Image B5:Set G)) :
    ⁅Q₅ d B5,zpowers t⁆=d.toTypeRuSetup.U := by
  let P:=Q₅ d B5
  let M:=⁅P,zpowers t⁆
  let A:=B5Image B5
  have hMU:M≤d.toTypeRuSetup.U := by
    rw [←firstCore_derived d B5]
    exact commutator_mono le_sup_right (zpowers_le.mpr (show t∈fiveHyperplane d B5 from (show Q₀ d≤fiveHyperplane d B5 from le_sup_left) ht))
  have hMP:M≤P:=hMU.trans (U_le_Q₅ d B5)
  have hCc : Nat.card ((centralizer ({t}:Set G)).subgroupOf P)=32 := by
    have he : (centralizer ({t}:Set G)).subgroupOf P=d.toTypeRuSetup.U.subgroupOf P := by
      ext x
      have hh:=Q₅_fixed_root_centralizer d B5 t ht hn
      change (x:G)∈centralizer ({t}:Set G) ↔ (x:G)∈d.toTypeRuSetup.U
      rw [←hh]
      exact ⟨fun h=>⟨x.property,h⟩,fun h=>h.2⟩
    rw [he,Nat.card_congr (subgroupOfEquivOfLe (U_le_Q₅ d B5)).toEquiv,d.ru2.card_U d.card_Z]
  have hlow:16≤Nat.card M := by
    have hh:=card_le_commutator_card_mul_centralizer P t
    rw [card_Q₅,hCc] at hh
    change 512≤Nat.card M*32 at hh
    omega
  have hZM:=Q₅_normal_contains_Z d B5 M hMP
    (normalizer_commutator_ge_left _ _) (by omega)
  have hAM:A≤normalizer M := by
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [M]
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
      (normalizer_commutator_ge_right d.toTypeRuSetup.Q A ha),MonoidHom.map_zpowers]
    have htfix : MulAut.conj a t=t := mul_inv_eq_iff_eq_mul.mpr (hf a ha)
    change ⁅P,zpowers (MulAut.conj a t)⁆=⁅P,zpowers t⁆
    rw [htfix]
  let : MulDistribMulAction A M := conjMulDistribMulActionOfLeNormalizer A M hAM
  let F:=FixedPoints.subgroup A M
  have hF : F.map M.subtype=d.toTypeRuSetup.Z := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      have hxc : (x:G)∈CQ B5 := by
        refine ⟨Q₅_le_Q d B5 (hMP x.property),?_⟩
        intro a ha
        have he:=congrArg (fun y:M=>(y:G)) (hx ⟨a,ha⟩)
        change a*(x:G)*a⁻¹=(x:G) at he
        exact mul_inv_eq_iff_eq_mul.mp he
      exact (Q₅_inf_CQ d B5).le ⟨hMP x.property,hxc⟩
    · intro z hz
      refine ⟨⟨z,hZM hz⟩,?_,rfl⟩
      intro a
      apply Subtype.ext
      change (a:G)*z*(a:G)⁻¹=z
      exact mul_inv_eq_iff_eq_mul.mpr ((map_subtype_le _ a.property) z hz).symm
  have hFc:Nat.card F=2 := by
    rw [←card_map_of_injective M.subtype_injective,hF,d.card_Z]
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hmod := (IsPGroup.of_card (p:=5) (n:=1) (show Nat.card A=5 from
    B5Image_card d.card_Z B5)).card_modEq_card_fixedPoints M
  change Nat.card M%5=Nat.card F%5 at hmod
  rw [hFc] at hmod
  have hdiv:Nat.card M∣2^5 := by
    have hh:=card_dvd_of_le hMU
    rwa [d.ru2.card_U d.card_Z] at hh
  obtain ⟨n,hn,hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hc:Nat.card M=32 := by
    interval_cases n <;> norm_num only [Nat.reducePow] at hcard <;> omega
  exact eq_of_le_of_card_ge hMU (by rw [hc,d.ru2.card_U d.card_Z])

variable {d} {p:Plane d}

/-- The original conjugate elementary group supplies an involutory residual seed. -/
theorem SourceChoice.exists_Q₅_involution (s:SourceChoice p)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃b:Q₅ d B5,(b:G)∈s.Dα ∧ b^2=1 ∧ (b:G)∉d.toTypeRuSetup.U := by
  have hnot : ¬s.Dα≤d.toTypeRuSetup.U := by
    intro h
    have hh : hat d s.Dα=⊥ := by
      apply bot_unique
      rintro _ ⟨x,hx,rfl⟩
      exact (hatMap_eq_one d x).mpr (h hx)
    have hc:=s.hat_Dα_card
    rw [hh,card_bot] at hc
    contradiction
  obtain ⟨b,hb,hbU⟩ := Set.not_subset.mp hnot
  have hbH : b∈d.toTypeRuSetup.H := pCoreIn_le 2 _ hb.2
  have hb5 : b∈Q₅ d B5 := by
    have hh := s.hat_Dα_le_Q₅ B5 hi (mem_map_of_mem (hatMap d) (show
      (⟨b,hbH⟩:d.toTypeRuSetup.H)∈s.Dα.subgroupOf d.toTypeRuSetup.H from hb))
    obtain ⟨x,hx,he⟩ := hh
    have hu : b*(x:G)⁻¹∈d.toTypeRuSetup.U := by
      apply (hatMap_eq_one d ((⟨b,hbH⟩:d.toTypeRuSetup.H)*x⁻¹)).mp
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hh := (Q₅ d B5).mul_mem (U_le_Q₅ d B5 hu) hx
    change b*(x:G)⁻¹*(x:G)∈Q₅ d B5 at hh
    simpa only [inv_mul_cancel_right] using hh
  refine ⟨⟨b,hb5⟩,hb,?_,hbU⟩
  apply Subtype.ext
  obtain ⟨u,hu,he⟩ := hb.1
  have hu2 : u^2=1 := by
    let := d.elementary_U
    exact elemPow_eq_one_of_isElementaryAbelian (p:=2) u hu
  change b^2=1
  rw [←he,←map_pow,hu2,map_one]

end CFSG.Quasithin.ChapterJ.RuSubgroup

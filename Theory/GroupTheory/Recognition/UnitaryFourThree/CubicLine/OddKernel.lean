module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.QuaternionNormalizer

/-!
# The fixed cubic line in the actual odd core

The odd core D of N_G(W) contains and centralizes W. Its intersection with
C_G(z) centralizes the normal quaternion subgroup C_Q(W). An intersection
of order nine would force that quaternion eight into the order-eighteen
centralizer of an independent cubic nine, which is impossible. Hence the
intersection is exactly W, and z inverts the abelian quotient D/W.

This is the second paragraph of Aschbacher, Sporadic Groups (1994),45.8,p246.
No odd-core order or whole-normalizer model is assumed.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine
variable {G:Type*} [Group G] [Finite G]
theorem oddKernel_odd (W:Subgroup G) : Odd (Nat.card (oddKernel W)) := by
  change Odd (Nat.card ((pPrimeCore 2 (normalizer (W:Set G))).map _))
  rw [card_map_of_injective (normalizer (W:Set G)).subtype_injective]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p:=2))
omit [Finite G] in
theorem le_oddKernel (W:Subgroup G) (hW:Nat.card W=3) : W≤oddKernel W := by
  let N:=normalizer (W:Set G)
  have hWN:W≤N:=W.le_normalizer
  let : (W.subgroupOf N).Normal:=(normal_subgroupOf_iff_le_normalizer hWN).mpr le_rfl
  have ho:Nat.Coprime 2 (Nat.card (W.subgroupOf N)):=by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv,hW]
    decide
  have hi:W.subgroupOf N≤pPrimeCore 2 N:=le_sSup ⟨inferInstance,ho⟩
  have hm:=map_mono (f:=N.subtype) hi
  rwa [map_subgroupOf_eq_of_le hWN] at hm

omit [Finite G] in
theorem normalizer_normalizes_oddKernel (W:Subgroup G) :
    normalizer (W:Set G)≤normalizer (oddKernel W:Set G) :=
  (normalizer (W:Set G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (normalizer (W:Set G))
      (pPrimeCore 2 (normalizer (W:Set G))))

theorem oddKernel_centralizes (W:Subgroup G) (hW:Nat.card W=3) :
    oddKernel W≤Subgroup.centralizer (W:Set G) := by
  let D:=oddKernel W
  let f:D→*MulAut W:=W.normalizerMonoidHom.comp (inclusion (map_subtype_le _))
  let : IsCyclic W:=isCyclic_of_prime_card hW
  have ha:Nat.card (MulAut W)=2:=by rw [IsCyclic.card_mulAut,hW];decide
  have hd:Nat.card f.range∣2:=ha ▸ f.range.card_subgroup_dvd_card
  have ho:Odd (Nat.card f.range):=(oddKernel_odd W).of_dvd_nat (card_range_dvd f)
  have he:Nat.card f.range=1:=Nat.dvd_one.mp (ho.coprime_two_right.dvd_of_dvd_mul_right (by simpa using hd))
  have hb:f.range=⊥:=Subgroup.card_eq_one.mp he
  intro d hd w hw
  have hf:f ⟨d,hd⟩=1:=by
    have hh: f ⟨d,hd⟩∈f.range:=⟨⟨d,hd⟩,rfl⟩
    simpa [hb] using hh
  have hh:=congrArg (fun a:MulAut W=>(a ⟨w,hw⟩:G)) hf
  change d*w*d⁻¹=w at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_line_oddKernel_fixed (W:Subgroup G) (hW:Nat.card W=3)
    (hWH:W≤centralizer z)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2)) :
    CubicLine.oddKernel W⊓centralizer z=W := by
  let D:=CubicLine.oddKernel W
  let A:=D⊓centralizer z
  let C:=core z⊓Subgroup.centralizer (W:Set G)
  let N:=normalizer (W:Set G)⊓centralizer z
  have hDN:D≤normalizer (W:Set G):=map_subtype_le _
  have hAN:A≤N:=inf_le_inf hDN le_rfl
  have hAH:A≤centralizer z:=inf_le_right
  have hCC:Nat.card C=8:=by
    rw [Nat.card_congr hfixed.some.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hCH:C≤centralizer z:=inf_le_left.trans ((pCoreIn_le 2 (residual z)).trans (map_subtype_le _))
  have hCN:C≤N:=le_inf (inf_le_right.trans (centralizer_le_normalizer _)) hCH
  have hNA:N≤normalizer (A:Set G):=
    (le_inf (inf_le_left.trans (CubicLine.normalizer_normalizes_oddKernel W))
      (inf_le_right.trans (centralizer z).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hNC:N≤normalizer (C:Set G):=
    (le_inf (inf_le_right.trans CentralizerHypothesis.centralizer_normalizes_core)
      (inf_le_left.trans (normalizer_le_normalizer_centralizer W))).trans inf_normalizer_le_normalizer_inf
  have ho:Odd (Nat.card A):=(CubicLine.oddKernel_odd W).of_dvd_nat (card_dvd_of_le inf_le_left)
  have hdis:Disjoint C A:=disjoint_of_coprime_natCard (by
    rw [hCC]
    exact ho.coprime_two_left.pow_left 3)
  have hcomm:C≤Subgroup.centralizer (A:Set G):=by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [←hdis.eq_bot]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp (hAN.trans hNC))
      (le_normalizer_iff_commutator_le_right.mp (hCN.trans hNA))
  have hd:Nat.card A∣9:=by
    have hd:=card_dvd_of_le hAH
    rw [h.centralizer_card] at hd
    exact (ho.coprime_two_right.pow_right 7).dvd_mul_left.mp hd
  have hne:Nat.card A≠9:=by
    intro ha
    have hh:=h.toCentralizerHypothesis.cubic_centralizer A ha hAH
    have hprod:Nat.card (A⊔zpowers z:Subgroup G)=18:=by
      have hc:zpowers z≤Subgroup.centralizer (A:Set G):=
        zpowers_le.mpr (fun x hx=>mem_centralizer_singleton_iff.mp (hAH hx))
      rw [card_sup_eq_mul_of_normalizes_of_disjoint A (zpowers z)
        (hc.trans (centralizer_le_normalizer _))
        (disjoint_of_coprime_natCard (by rw [ha,Nat.card_zpowers,h.involution];decide)),ha,
        Nat.card_zpowers,h.involution]
    have hd:=card_dvd_of_le ((le_inf hCH hcomm).trans hh.le)
    rw [hCC,hprod] at hd
    norm_num at hd
  have hdiv3:Nat.card A∣3:=by
    have hh:=Nat.mem_divisors.mpr ⟨hd,(by decide:9≠0)⟩
    have hs:Nat.divisors 9={1,3,9}:=by decide
    simp only [hs,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh|hh|hh
    · rw [hh];exact one_dvd _
    · rw [hh]
    · exact (hne hh).elim
  have hWA:W≤A:=le_inf (CubicLine.le_oddKernel W hW) hWH
  exact (eq_of_le_of_card_ge hWA (by rw [hW];exact Nat.le_of_dvd (by decide) hdiv3)).symm
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_line_oddKernel_inversion (W:Subgroup G) (hW:Nat.card W=3)
    (hWH:W≤centralizer z)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2)) :
    (∀d∈CubicLine.oddKernel W,z*d*z⁻¹*d∈W) ∧
      ⁅CubicLine.oddKernel W,CubicLine.oddKernel W⁆≤W := by
  let D:=CubicLine.oddKernel W
  have hZD:z∈normalizer (D:Set G):=CubicLine.normalizer_normalizes_oddKernel W
    (centralizer_le_normalizer _ (fun w hw=>mem_centralizer_singleton_iff.mp (hWH hw)))
  let a:=D.normalizerMonoidHom ⟨z,hZD⟩
  let C:=W.subgroupOf D
  have hWD:W≤D:=CubicLine.le_oddKernel W hW
  have hcen:C≤center D:=by
    intro w hw
    apply mem_center_iff.mpr
    intro d
    exact Subtype.ext ((CubicLine.oddKernel_centralizes W hW d.property) w hw).symm
  let : C.Normal:=⟨fun w hw d=>by
    rw [mem_center_iff.mp (hcen hw) d,mul_inv_cancel_right]
    exact hw⟩
  have ha:Function.Involutive a:=by
    intro d
    apply Subtype.ext
    change z*(z*(d:G)*z⁻¹)*z⁻¹=(d:G)
    have hz2:z*z=1:=by simpa only [pow_two,h.involution] using pow_orderOf_eq_one z
    have hzI:z⁻¹=z:=inv_eq_of_mul_eq_one_left hz2
    rw [hzI]
    calc
      z*(z*(d:G)*z)*z=(z*z)*(d:G)*(z*z):=by group
      _=d:=by rw [hz2,one_mul,mul_one]
  have hf (d:D):a d=d ↔ d∈C:=by
    constructor
    · intro hd
      have hh:z*(d:G)*z⁻¹=(d:G):=congrArg Subtype.val hd
      exact (h.cubic_line_oddKernel_fixed W hW hWH hfixed).le
        ⟨d.property,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm⟩
    · intro hd
      apply Subtype.ext
      change z*(d:G)*z⁻¹=(d:G)
      have hh:(d:G)*z=z*(d:G):=mem_centralizer_singleton_iff.mp (hWH hd)
      rw [←hh,mul_inv_cancel_right]
  have ho:Odd (Nat.card C):=by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWD).toEquiv,hW]
    decide
  obtain ⟨hi,hc⟩:=a.quotient_inversion_of_odd_fixed_kernel ha C ho hf
  constructor
  · intro d hd
    exact hi ⟨d,hd⟩
  · have hm:=map_mono (f:=D.subtype) hc
    rw [map_commutator_eq,map_subgroupOf_eq_of_le hWD] at hm
    simpa only [D.range_subtype] using hm
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType

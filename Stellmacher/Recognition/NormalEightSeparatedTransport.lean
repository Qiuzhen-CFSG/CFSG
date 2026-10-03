module

public import Stellmacher.Recognition.NormalEightSeparatedFusion
public import Stellmacher.Recognition.NormalEightNormalImageTransport
public import Theory.GroupTheory.PGroup.SmallElementaryNormal
public import Theory.GroupTheory.FusedFourTransport

/-!
# Centralizer transport in the separated case

A two-subgroup containing a conjugate of the normal four and centralizing
one of its involutions normalizes that four. For a noncentral involution,
transport the explicit local centralizer control by conjugation. For a
central involution, transport the two-subgroup into the original Sylow;
normality of the actual odd-core quotient image identifies the returning
four. This argument does not assume fusion of the involutions.

Only the unconditional Sylow transport lemma from `FusedFourTransport` is
used, not its fused-four geometric conclusions.

Source: Janko–Thompson, Math. Z. 113 (1970), §6, printed p.395, and the
normalizer construction in Lemma 5.1, printed p.394.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedTransport

open Subgroup NormalFourCentralOmegaTwo NormalEightSeparatedFusion
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

/-- An involution in the Sylow center generates its central omega line. -/
public theorem centralOmega_eq_zpowers
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2) :
    centralOmega S = zpowers (z : G) := by
  have hmem : (z : G) ∈ centralOmega S := by
    apply mem_map_of_mem (S : Subgroup G).subtype
    refine mem_map.mpr ⟨⟨z, hzC⟩, ?_, rfl⟩
    apply Subgroup.subset_closure
    change (⟨z, hzC⟩ : center S) ^ (2 ^ 1) = 1
    apply Subtype.ext
    change z ^ 2 = 1
    simpa only [hz] using pow_orderOf_eq_one z
  symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr hmem)
  rw [card_centralOmega S, hZ, Nat.card_zpowers, orderOf_coe, hz]

/-- Returning conjugates through any central Sylow involution are fixed.
Normality remains a hypothesis on the actual quotient image. -/
public theorem conjugate_four_eq_of_mem_central_involution
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal]
    (g : G)
    (hreturn : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hzmem : (z : G) ∈
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) :
    (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
      W.map (S : Subgroup G).subtype := by
  apply NormalEightNormalImage.conjugate_four_eq_of_centralOmega_le
    S hno hZ W hW hunique g hreturn
  rw [centralOmega_eq_zpowers S hZ z hzC hz]
  exact zpowers_le.mpr hzmem

omit [Finite G] in
private theorem conj_map_comp (W : Subgroup G) (g k : G) :
    (W.map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      W.map (MulAut.conj (k * g)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
/-- Local centralizer control transports to the noncentral involutions of
any ambient conjugate of the four. -/
public theorem conjugate_centralized_by_two_overgroup
    (S : Sylow 2 G) (W : Subgroup S)
    (hcontrol : LocalCentralizerControl S W)
    (g : G) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2) (hiC : i ∉ center S)
    (R : Subgroup G) (hR : IsPGroup 2 R)
    (hWR : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤ R)
    (hRC : R ≤ centralizer ({(MulAut.conj g) (i : G)} : Set G)) :
    R ≤ centralizer
      (((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) : Set G) := by
  let f := MulAut.conj g
  let R' := R.map f.symm.toMonoidHom
  have hWR' : W.map (S : Subgroup G).subtype ≤ R' := by
    intro w hw
    exact ⟨f w, hWR (mem_map_of_mem _ hw), f.symm_apply_apply w⟩
  have hRC' : R' ≤ centralizer ({(i : G)} : Set G) := by
    rintro x ⟨r, hr, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg f.symm (mem_centralizer_singleton_iff.mp (hRC hr))
    simpa only [map_mul, ← show f = MulAut.conj g from rfl,
      MulEquiv.symm_apply_apply, MulEquiv.coe_toMonoidHom] using hh
  have hc := hcontrol i hiW hi hiC R' (hR.map _) hWR' hRC'
  rintro r hr w ⟨u, hu, rfl⟩
  have hh := congrArg f (hc (mem_map_of_mem f.symm.toMonoidHom hr) u hu)
  simpa only [map_mul, MulEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom] using hh

/-- Every two-overgroup centralizing an involution of a conjugate four
normalizes that four. No fusion hypothesis is used. -/
public theorem conjugate_normalized_by_centralizing_two_overgroup
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal]
    (hcontrol : LocalCentralizerControl S W)
    (g : G) (R : Subgroup G) (hR : IsPGroup 2 R)
    (hWR : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤ R)
    (x : G)
    (hx : x ∈ (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom)
    (hx1 : x ≠ 1) (hRC : R ≤ centralizer ({x} : Set G)) :
    R ≤ normalizer
      (((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) : Set G) := by
  obtain ⟨_, ⟨i, hiW, rfl⟩, rfl⟩ := hx
  have hi1 : i ≠ 1 := by rintro rfl; exact hx1 (map_one _)
  have hi : orderOf i = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) i hiW) hi1
  by_cases hiC : i ∈ center S
  · let W₀ := W.map (S : Subgroup G).subtype
    let V := W₀.map (MulAut.conj g).toMonoidHom
    have hxi : IsConj ((MulAut.conj g) (i : G)) (i : G) :=
      (isConj_iff.mpr ⟨g, rfl⟩).symm
    obtain ⟨k, hkS, hki⟩ := S.transport_centralizing_two_subgroup i hiC
      ((MulAut.conj g) (i : G)) hxi R hR hRC
    have hVk : V.map (MulAut.conj k).toMonoidHom = W₀ := by
      rw [conj_map_comp]
      refine conjugate_four_eq_of_mem_central_involution S hno hZ W hW hunique
        (k * g) ?_ i hiC hi ?_
      · rw [← conj_map_comp]
        exact (map_mono hWR).trans hkS
      · rw [← conj_map_comp, ← hki]
        exact mem_map_of_mem _ (mem_map_of_mem _ (mem_map_of_mem _ hiW))
    have hWN : (S : Subgroup G) ≤ normalizer (W₀ : Set G) := by
      simpa only [W.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
        W.le_normalizer_map (S : Subgroup G).subtype
    intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply map_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
    change (V.map (MulAut.conj r).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      V.map (MulAut.conj k).toMonoidHom
    have hswitch : (V.map (MulAut.conj r).toMonoidHom).map
        (MulAut.conj k).toMonoidHom =
        (V.map (MulAut.conj k).toMonoidHom).map
          (MulAut.conj ((MulAut.conj k) r)).toMonoidHom := by
      rw [conj_map_comp V r k, conj_map_comp V k ((MulAut.conj k) r)]
      have he : k * r = (MulAut.conj k) r * k := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [he]
    rw [hswitch, hVk]
    exact mem_normalizer_iff_map_conj_eq.mp (hWN (hkS (mem_map_of_mem _ hr)))
  · exact (conjugate_centralized_by_two_overgroup S W hcontrol g i hiW hi hiC
      R hR hWR hRC).trans (Subgroup.centralizer_le_normalizer _)


/-- Under returning-image and local centralizer control, every conjugate
returning to the Sylow commutes with the original four. -/
public theorem returning_conjugate_le_centralizer
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal]
    (hcontrol : LocalCentralizerControl S W)
    (g : G)
    (hVS : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G)) :
    (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (W.map (S : Subgroup G).subtype : Set G) := by
  let W₀ := W.map (S : Subgroup G).subtype
  let V := W₀.map (MulAut.conj g).toMonoidHom
  let VS := V.subgroupOf (S : Subgroup G)
  let C := centralizer (W : Set S)
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  by_cases heq : V = W₀
  · change V ≤ centralizer (W₀ : Set G)
    rw [heq]
    exact W₀.le_centralizer
  have hd : Disjoint (centralOmega S) V :=
    NormalEightNormalImage.centralOmega_disjoint_of_distinct_conjugate_four
      S hno hZ W hW hunique g hVS heq
  have hVC : Nat.card VS = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVS).toEquiv,
      card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective (S : Subgroup G).subtype_injective, hW]
  have hi : C.index ≤ 2 := centralizer_index_le_two_of_normal_four S.isPGroup' W hW
  have hri : (C.subgroupOf VS).index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero C.index_ne_zero_of_finite)
      (C.relIndex_dvd_index_of_normal VS)).trans hi
  have hc := (C.subgroupOf VS).card_mul_index
  rw [hVC] at hc
  have htwo : 1 < Nat.card (C.subgroupOf VS) := by nlinarith
  let : Nontrivial (C.subgroupOf VS) := Finite.one_lt_card_iff_nontrivial.mp htwo
  obtain ⟨a, ha⟩ := exists_ne (1 : C.subgroupOf VS)
  let x : G := (((a : VS) : S) : G)
  have hxV : x ∈ V := (a : VS).property
  have hx1 : x ≠ 1 := fun h => ha (Subtype.ext (Subtype.ext (Subtype.ext h)))
  have hxC : x ∈ centralizer (W₀ : Set G) := by
    rintro w ⟨e, he, rfl⟩
    exact congrArg Subtype.val (a.property e he)
  have hRS : W₀ ⊔ V ≤ (S : Subgroup G) := sup_le (map_subtype_le W) hVS
  have hp : IsPGroup 2 (W₀ ⊔ V : Subgroup G) :=
    S.isPGroup'.of_injective (inclusion hRS) (inclusion_injective hRS)
  have hRC : W₀ ⊔ V ≤ centralizer ({x} : Set G) := by
    apply sup_le
    · intro w hw
      exact mem_centralizer_singleton_iff.mpr (hxC w hw)
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (V.le_centralizer hv x hxV).symm
  have hWV : W₀ ≤ normalizer (V : Set G) := le_sup_left.trans
    (conjugate_normalized_by_centralizing_two_overgroup S hno hZ W hW hunique hcontrol
      g (W₀ ⊔ V) hp le_sup_right x hxV hx1 hRC)
  have hcommZ : ⁅W₀, V⁆ ≤ centralOmega S := by
    apply commutator_le.mpr
    rintro w ⟨u, hu, rfl⟩ v hv
    let s : S := ⟨v, hVS hv⟩
    have hmem : ⁅u, s⁆ ∈ ⁅W, (⊤ : Subgroup S)⁆ :=
      commutator_mem_commutator hu (mem_top s)
    have hcenter : ⁅u, s⁆ ∈ center S :=
      commutator_le_center_of_elementary_card_le_four S.isPGroup' W hW.le hmem
    have hWmem : ⁅u, s⁆ ∈ W := commutator_le_left W ⊤ hmem
    have hΩ : ⁅u, s⁆ ∈ (omega₁ (center S) (p := 2)).map (center S).subtype := by
      refine mem_map.mpr ⟨⟨⁅u, s⁆, hcenter⟩, ?_, rfl⟩
      apply Subgroup.subset_closure
      change (⟨⁅u, s⁆, hcenter⟩ : center S) ^ (2 ^ 1) = 1
      apply Subtype.ext
      change ⁅u, s⁆ ^ 2 = 1
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hWmem
    exact mem_map_of_mem (S : Subgroup G).subtype hΩ
  have hcommV : ⁅W₀, V⁆ ≤ V := le_normalizer_iff_commutator_le_right.mp hWV
  have hcomm : ⁅W₀, V⁆ = ⊥ :=
    le_bot_iff.mp ((disjoint_iff.mp hd) ▸ le_inf hcommZ hcommV)
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)

end Stellmacher.Recognition.NormalEightSeparatedTransport

module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleLinear
public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary
public import Theory.Mathieu.M24.Properties.InvolutionFixedOrders
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart

/-!
# The original fixed line through the central quotient

The A₆ quotient forces nine to divide the order of the literal L_v image.
Consequently any central-quotient model with nine-free involution centralizers
kills C_{V_v}(L_v). For M₂₄ the proved odd covering kernel makes this
impossible, excluding that model. For Ru it identifies the projection kernel
on the original order-32 V_v with the original fixed line, giving image order
sixteen. The preferred-point application retains V, C_V(L), conjugation and
the canonical central quotient.

Source: Aschbacher--Smith, proof of 12.6.12, printed pp.825--826, and I.1.3,
printed p.407. This is a partial model exclusion, not 12.6.2 or 12.6.23.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- An involution-centralizer obstruction puts the original fixed line in the
center of K_v, through its literal central projection. -/
theorem SourceHypothesis.nonsingular_fixed_line_le_center_of_centralizers
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    {F : Type*} [Group F] [Finite F]
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* F)
    (hF : ∀ t : F, orderOf t = 2 → ¬ 9 ∣ Nat.card (centralizer ({t} : Set F))) :
    (ZV (Lv L (v : G)) (Vv L V (v : G))).subgroupOf (Kv (v : G)) ≤
      center (Kv (v : G)) := by
  let C := Kv (v : G)
  let P := (Lv L (v : G)).subgroupOf C
  let q := QuotientGroup.mk' (center C)
  let f := e.toMonoidHom.comp q
  let B := (P.map q).map e.toMonoidHom
  have h9 : 9 ∣ Nat.card B := by
    rw [card_map_of_injective e.injective]
    obtain ⟨_,⟨eA⟩,_⟩ := H.nonsingular_centralQuotient_local_marking D v hv
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (P.map q)))
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  intro z hz
  by_contra hzc
  have hne : f z ≠ 1 := by
    intro he
    apply hzc
    apply (QuotientGroup.eq_one_iff z).mp
    exact e.injective (he.trans e.map_one.symm)
  have hzV : (z : G) ∈ V := Vv_le_V H.chosen.normalizes _ hz.1
  have hzsq : z ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (z : G) hzV)
  have ho : orderOf (f z) = 2 := orderOf_eq_prime (by rw [←map_pow,hzsq,map_one]) hne
  apply hF (f z) ho
  apply h9.trans (card_dvd_of_le (show B ≤ centralizer ({f z} : Set F) from ?_))
  rintro _ ⟨y,⟨b,hb,rfl⟩,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  change f b * f z = f z * f b
  rw [←map_mul,←map_mul]
  exact congrArg f (Subtype.ext (mem_centralizer_iff.mp hz.2 (b : G) hb))

/-- If the marked central quotient has nine-free involution centralizers,
the actual K_v center has even order. -/
theorem SourceHypothesis.nonsingular_even_center_of_centralizers
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    {F : Type*} [Group F] [Finite F]
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* F)
    (hF : ∀ t : F, orderOf t = 2 → ¬ 9 ∣ Nat.card (centralizer ({t} : Set F))) :
    2 ∣ Nat.card (center (Kv (v : G))) := by
  have hle := H.nonsingular_fixed_line_le_center_of_centralizers D v hv e hF
  have hd := card_dvd_of_le hle
  have hFC : ZV (Lv L (v : G)) (Vv L V (v : G)) ≤ Kv (v : G) :=
    inf_le_left.trans (H.nonsingular_component_rank D v hv).1
  rwa [Nat.card_congr (subgroupOfEquivOfLe hFC).toEquiv,
    D.nonsingular_moved_fixed_card H.chosen v hv] at hd

private theorem mathieu24_centralizer_not_nine (t : Sporadic.Mathieu.M24)
    (ht : orderOf t = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({t} : Set Sporadic.Mathieu.M24)) := by
  have hi := MulAut.conj_injective_of_center_eq_bot
    Sporadic.Mathieu.M24InvolutionCentralizers.center_eq_bot
  have ho : orderOf (MulAut.conj t) = 2 := (orderOf_injective MulAut.conj hi t).trans ht
  have hh := Sporadic.Mathieu.m24_involution_not_nine_dvd_fixed_card (MulAut.conj t) ho
  simpa only [MulAut.fixedSubgroup_conj] using hh

/-- The actual M24 multiplier and involution centralizers exclude its row. -/
theorem SourceHypothesis.nonsingular_not_mathieu24_centralQuotient
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    ¬ Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.Mathieu.M24) := by
  let := hK
  rintro ⟨e⟩
  have hn := Sporadic.Mathieu.SchurMultipliers.m24_cover_kernel_not_two
    (PerfectCentralCovering.centralQuotientCover e)
  rw [PerfectCentralCovering.centralQuotientCover_ker] at hn
  exact hn (H.nonsingular_even_center_of_centralizers D v hv e mathieu24_centralizer_not_nine)

/-- In the Ru row the original local fixed line lies in Z(K_v). -/
theorem SourceHypothesis.nonsingular_ru_fixed_line_le_center
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hmodel : Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model)) :
    (ZV (Lv L (v : G)) (Vv L V (v : G))).subgroupOf (Kv (v : G)) ≤
      center (Kv (v : G)) := by
  obtain ⟨e⟩ := hmodel
  exact H.nonsingular_fixed_line_le_center_of_centralizers D v hv e
    Rudvalis.InvolutionCentralizers.centralizer_not_nine

/-- The Ru projection has exactly the original fixed line as its kernel on
V_v, and the moved image has order sixteen. -/
theorem SourceHypothesis.nonsingular_ru_moved_image_card
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hmodel : Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model)) :
    let C := Kv (v : G)
    Nat.card (((Vv L V (v : G)).subgroupOf C).map (QuotientGroup.mk' (center C))) = 16 := by
  let C := Kv (v : G)
  let W := Vv L V (v : G)
  let Z := ZV (Lv L (v : G)) W
  have hWC : W ≤ C := (H.nonsingular_component_rank D v hv).1
  have hLC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L _
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  let f := (QuotientGroup.mk' (center C)).comp (inclusion hWC)
  have hk : f.ker = Z.subgroupOf W := by
    ext w
    change QuotientGroup.mk' (center C) (inclusion hWC w) = 1 ↔ (w : G) ∈ Z
    constructor
    · intro hz
      have hz := (QuotientGroup.eq_one_iff _).mp hz
      refine ⟨w.property,?_⟩
      intro b hb
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨b,hLC hb⟩)
    · intro hz
      exact (QuotientGroup.eq_one_iff _).mpr
        (H.nonsingular_ru_fixed_line_le_center D v hv hmodel hz)
  have hc := f.ker.card_mul_index
  rw [index_ker,hk,Nat.card_congr (subgroupOfEquivOfLe (show Z ≤ W from inf_le_left)).toEquiv,
    D.nonsingular_moved_fixed_card H.chosen v hv,D.nonsingular_moved_card H.chosen v hv] at hc
  have hr : Nat.card f.range = 16 := by omega
  simpa only [f,MonoidHom.range_comp,inclusion_range] using hr
end CFSG.Quasithin.Chapter12.Section06

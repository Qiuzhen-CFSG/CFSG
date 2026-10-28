module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree.FixedModule
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.CubicNormality
public import Theory.SpecificGroups.PSL3Two.OuterThreeFree


/-!
# Normalizer control from the actual second-parabolic cubic

The action of Y₀ on V₂ has index three. Its embedding in L, whose literal
two-core quotient has order 168, rules out elements of order nine and supplies
an order-three lift acting nontrivially. Conjugation by the exchanged element
places this cubic outside C_G(V₁) in N_G(V₁). Original 1.2.1--2 then makes L
normal in that whole normalizer, preserving the actual C-component inclusion.

Source: Aschbacher--Smith 15.1.24(2), p.1101, using 1.2.1--2, pp.504--505.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The actual parabolic residual contains a cubic moving V₂. Its order
is proved in the literal two-core quotient, so the lift retains order three. -/
theorem ExchangedSource.linearThree_moving_cubic
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative) :
    ∃ y : G, y ∈ d.linearThreeY ∧ orderOf y = 3 ∧
      y ∉ centralizer (d.nineMovingPlane : Set G) := by
  let Y := d.linearThreeY
  let C := centralizer (d.nineMovingPlane : Set G)
  let K := C.subgroupOf Y
  obtain ⟨_,hi,_⟩ := s.linearThree_moving_action_kernel (h := h) sp hTM a
  have hm := (s.linearThree_residual_action (h := h) sp hTM a).2.1
  have hYn : Y ≤ normalizer (d.nineMovingPlane : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hm.le
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (hYn.trans (normalizer_le_normalizer_centralizer _))
  have hcard : Nat.card (Y ⧸ K) = 3 := hi
  let q := QuotientGroup.mk' K
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hcard])
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective K z
  have hYL : Y ≤ d.L := (map_subtype_le _).trans inf_le_right
  obtain ⟨e,_⟩ := a.marked_parabolic
  let f := (QuotientGroup.mk' (pCore 2 d.L)).comp (inclusion hYL)
  have hk : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hYL)
  have hno (x : Y) : orderOf x ≠ 3*3 := by
    intro hx
    have ho := (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x
      (by rw [hx]; decide)).trans hx
    have hd := orderOf_dvd_natCard (e (f x))
    rw [e.orderOf_eq,ho,Matrix.PSL3Two.card_SL] at hd
    norm_num at hd
  obtain ⟨b,hb,hbq⟩ := q.exists_prime_order_lift_of_no_prime_square_order Nat.prime_three hno y hz
  refine ⟨b,b.property,(Y.orderOf_coe b).trans hb,?_⟩
  intro hc
  have he : q b = 1 := (QuotientGroup.eq_one_iff b).mpr hc
  rw [he,orderOf_one] at hbq
  omega

/-- The exchanged cubic is in the literal fixed-plane normalizer and outside
its centralizer. -/
theorem ExchangedSource.linearThree_external_cubic
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ∃ x : normalizer (d.nineFixedPlane : Set G), orderOf x = 3 ∧
      (x : G) ∈ d.linearThreeY.map (MulAut.conj t).toMonoidHom ∧
      (x : G) ∉ centralizer (d.nineFixedPlane : Set G) := by
  obtain ⟨y,hy,hy3,hyc⟩ := s.linearThree_moving_cubic (h := h) sp hTM a
  have hm := (s.linearThree_exchanged_action (h := h) sp hTM a ht htS).2.2
  have hn := le_normalizer_iff_commutator_le_left.mpr hm.le
  let x : G := MulAut.conj t y
  have hx : x ∈ d.linearThreeY.map (MulAut.conj t).toMonoidHom := mem_map_of_mem _ hy
  refine ⟨⟨x,hn hx⟩,?_,hx,?_⟩
  · exact ((normalizer (d.nineFixedPlane : Set G)).orderOf_coe _).symm.trans
      (((MulAut.conj t).orderOf_eq y).trans hy3)
  · intro hc
    apply hyc
    intro v hv
    have hh := hc (MulAut.conj t v) (by
      rw [←(s.exchanges t ht htS).2]
      exact mem_map_of_mem _ hv)
    apply (MulAut.conj t).injective
    simpa only [map_mul] using hh

/-- An actual external cubic makes the selected block normal in N_G(V₁). -/
theorem ExchangedSource.linearThree_normalizer_control
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative) :
    normalizer (d.nineFixedPlane : Set G) ≤ normalizer (d.L : Set G) := by
  let N := normalizer (d.nineFixedPlane : Set G)
  let C := centralizer (d.nineFixedPlane : Set G)
  let K := d.L.subgroupOf N
  have hLC := le_centralizer_iff.mp (a.fixedPlane_centralizes hTM h)
  have hLN : d.L ≤ N := hLC.trans (Subgroup.centralizer_le_normalizer _)
  have hK : K.IsCComponent := d.L_isCComponent_in_G1.in_normalizer_of_centralizes hLC
    (centralizer_le s.marked_le_fixed)
  let eK := subgroupOfEquivOfLe hLN
  let eQ := QuotientGroup.congr (pCore 2 K) (pCore 2 d.L) eK (pCore_map_iso 2 eK)
  obtain ⟨e,_⟩ := a.marked_parabolic
  let b := eQ.trans e
  let := s.quasisimple
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eQ.symm
  have hd : 3 ∣ Nat.card (K ⧸ pCore 2 K) := by
    rw [Nat.card_congr b.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  have hne : d.nineFixedPlane ≠ ⊥ := by
    intro he
    rcases s.sizes with hs | hs <;> have hc := hs.2.2.1 <;> rw [he,card_bot] at hc <;> omega
  let := h.elementary
  have hN := hG.twoLocal_sqtk ⟨d.nineFixedPlane,hne,
    (IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left,rfl⟩
  obtain ⟨t,ht,htS⟩ := s.exchange_exists
  obtain ⟨x,hx,_,hout⟩ := s.linearThree_external_cubic (h := h) sp hTM a ht htS
  have hn : K.Normal := Chapter1.Section02.component_normal_of_cubic_outside_normal
    hN (C.subgroupOf N) hK (comap_mono hLC) hd x hx hout
  exact (normal_subgroupOf_iff_le_normalizer hLN).mp hn

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

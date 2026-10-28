module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.CoreCentralizer
public import Theory.Representation.SL2FourNaturalOrbits.CubicFixedSpace
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.PResidualCommutator

/-!
# The original cubic action in the HS overgroup

Cauchy selects an actual cubic in L₁. The marked semilinear natural action
shows C_U(X₁)=Z(U), and coprime action gives U=[U,X₁]Z(U).
The hatted kernel places [Q,U] in Z(U); three-subgroups therefore makes
C_Q(X₁) centralize [U,X₁]. Normality of the original component and coprime
idempotence identify [Q,X₁]=[U,X₁], giving the original decomposition of Q.

Source: Aschbacher--Smith, proof of 14.3.33(3), printed p.1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem semilinear_cubic_fixed
    (a : Representation.SL2FourNatural.SemilinearNormalizer.specialField)
    (ha : orderOf a = 3) (v : Representation.SL2FourNatural.V)
    (hv : a.val v = v) : v = 0 := by
  let e := Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv
  have he3 : (e a) ^ 3 = 1 := by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hs : e a ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have hh : (Equiv.Perm.sign (e a)) ^ 2 * Equiv.Perm.sign (e a) = 1 := by
      simpa only [map_pow,map_one,pow_succ,pow_zero,one_mul,map_mul] using congrArg Equiv.Perm.sign he3
    simpa only [pow_two, Int.units_mul_self, one_mul] using hh
  rw [← Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv_special] at hs
  obtain ⟨b, ⟨A, hA⟩, hb⟩ := hs
  have he : b = a := e.injective hb
  have hAa : Representation.SL2FourNatural.action A = a.val := hA.trans (congrArg Subtype.val he)
  have hAo : orderOf A = 3 := by
    rw [← orderOf_injective Representation.SL2FourNatural.action Representation.SL2FourNatural.action_faithful A, hAa,
      Subgroup.orderOf_coe a, ha]
  exact Representation.SL2FourNatural.cubic_fixed_eq_zero A hAo v (hAa ▸ hv)

/-- Cauchy's theorem selects the original cubic in L₁. -/
theorem exists_point_cubic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    ∃ x : G, x ∈ F.Li L 1 ∧ orderOf x = 3 := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := F.Li L 1) 3 (by
    rw [point_residual_card h structural alternatives F s hne]
    decide)
  exact ⟨x,x.property,(orderOf_coe x).trans hx⟩

/-- Every cubic of H centralizes its cyclic Z(U). -/
theorem point_cubic_centralizes_center
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (x : G) (hx : x ∈ F.H) (hx3 : orderOf x = 3) :
    x ∈ centralizer (F.ZU : Set G) := by
  obtain ⟨e⟩ := center_model F s
  let := e.isCyclic.mpr inferInstance
  have hc : Nat.card F.ZU = 4 := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
  let a := F.ZU.normalizerMonoidHom ⟨x,F.H_normalizes_ZU hx⟩
  have ha3 : a ^ 3 = 1 := by
    change (F.ZU.normalizerMonoidHom _) ^ 3 = 1
    rw [← map_pow]
    have hh : (⟨x,F.H_normalizes_ZU hx⟩ : normalizer (F.ZU : Set G)) ^ 3 = 1 :=
      by
        apply Subtype.ext
        change x ^ 3 = 1
        simpa only [hx3] using pow_orderOf_eq_one x
    rw [hh, map_one]
  have ha2 : a ^ 2 = 1 := by
    have ht := pow_card_eq_one' (x := a)
    rw [IsCyclic.card_mulAut, hc] at ht
    exact ht
  have ha : a = 1 := by
    have hh : a ^ 2 * a = 1 := ha3
    simpa only [ha2,one_mul] using hh
  have hk : (⟨x,F.H_normalizes_ZU hx⟩ : normalizer (F.ZU : Set G)) ∈
      F.ZU.normalizerMonoidHom.ker := ha
  rwa [normalizerMonoidHom_ker] at hk

omit [Finite G] in
/-- A genuine cubic has no fixed vector on the literal U/Z(U). -/
theorem point_cubic_hat_fixed
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (x : F.H) (hx3 : orderOf x = 3) (v : F.Uhat)
    (hv : F.uhatAction x v = v) : v = 1 := by
  obtain ⟨e,c,he⟩ := s.natural
  let q := QuotientGroup.mk' (pCore 2 F.H)
  have hq3 : orderOf (q x) = 3 := by
    apply orderOf_eq_prime
    · simpa only [hx3,map_pow,map_one] using congrArg q (pow_orderOf_eq_one x)
    · intro hz
      have hxk : x ∈ pCore 2 F.H := (QuotientGroup.eq_one_iff x).mp hz
      have hc := (show IsPGroup 2 (pCore 2 F.H) from pCore_isPGroup).orderOf_coprime
        (by decide : Nat.Coprime 2 3) (⟨x,hxk⟩ : pCore 2 F.H)
      rw [← orderOf_coe, hx3] at hc
      norm_num at hc
  have hz : (c v).toAdd = 0 := semilinear_cubic_fixed (e (q x))
    ((e.orderOf_eq _).trans hq3) _ (by rw [← he, hv])
  exact c.injective (hz.trans c.map_one.symm)

/-- The actual cubic centralizer in U is precisely Z(U). -/
theorem closure_cubic_centralizer
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (x : G) (hx : x ∈ F.H) (hx3 : orderOf x = 3) :
    F.U ⊓ centralizer (zpowers x : Set G) = F.ZU := by
  have hxZ := point_cubic_centralizes_center F s x hx hx3
  apply le_antisymm ?_ (le_inf (map_subtype_le (center F.U))
    (le_centralizer_iff.mp (zpowers_le.mpr hxZ)))
  rintro u ⟨hu,huc⟩
  have huq : QuotientGroup.mk' (center F.U) (⟨u,hu⟩ : F.U) = 1 := by
    apply point_cubic_hat_fixed F s (⟨x,hx⟩ : F.H) ((orderOf_coe _).symm.trans hx3)
    rw [F.uhatAction_apply_mk]
    congr 1
    apply Subtype.ext
    change x * u * x⁻¹ = u
    rw [huc x (mem_zpowers x), mul_inv_cancel_right]
  exact mem_map_of_mem F.U.subtype ((QuotientGroup.eq_one_iff _).mp huq)

/-- Coprime action supplements the actual cubic commutator by the original center. -/
theorem closure_cubic_decomposition
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (x : G) (hx : x ∈ F.H) (hx3 : orderOf x = 3) :
    F.U = ⁅F.U,zpowers x⁆ ⊔ F.ZU := by
  have hp : IsPGroup 2 F.U := IsPGroup.of_card (n := 6) s.core_shape.card
  let := hp.isNilpotent
  have hn := (zpowers_le.mpr hx).trans (le_normalizer_conjugateSpanBy V F.H)
  have hc : Nat.Coprime (Nat.card (zpowers x)) (Nat.card F.U) := by
    rw [Nat.card_zpowers, hx3, s.core_shape.card]
    decide
  exact (eq_commutator_sup_centralizer_of_solvable_coprime F.U (zpowers x) hn
    inferInstance hc).trans (congrArg (⁅F.U,zpowers x⁆ ⊔ ·) (closure_cubic_centralizer F s x hx hx3))

omit [Finite G] in
/-- The original Q acts centrally on U, by the exact hatted kernel. -/
theorem point_core_closure_commutator_le_center
    (F : InvariantFlag T V 3) (s : LocalStructure L F) :
    ⁅F.H.pCoreIn 2,F.U⁆ ≤ F.ZU := by
  rw [commutator_le]
  rintro q ⟨a,ha,rfl⟩ u hu
  exact (F.mem_uhatAction_ker_iff a).mp (s.kernel.symm ▸ ha) u hu

/-- Three-subgroups converts the hatted kernel into the source centralization
of [U,X₁] by C_Q(X₁), with all subgroups in the original G. -/
theorem core_cubic_centralizes_commutator
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (x : G) (hx : x ∈ F.H) (hx3 : orderOf x = 3) :
    F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) ≤ centralizer ((⁅F.U,zpowers x⁆ : Subgroup G) : Set G) := by
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_commutator_eq_bot_of_rotate
  · have hz : ⁅zpowers x,F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp inf_le_right)
    rw [hz, commutator_bot_left]
  · apply bot_unique
    apply (commutator_mono ((commutator_mono inf_le_left le_rfl).trans
      (point_core_closure_commutator_le_center F s)) le_rfl).trans
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (zpowers_le.mpr (point_cubic_centralizes_center F s x hx hx3)))).le

omit [Finite G] in
/-- The literal point core lies in the original ambient Sylow. -/
theorem point_core_le_sylow [IsMulCommutative V] (F : InvariantFlag T V 3) :
    F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
  have hh := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
  change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
  rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)] at hh

/-- Coprime idempotence identifies [Q,X₁] with [U,X₁] in the original group. -/
theorem point_core_cubic_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3) :
    ⁅F.H.pCoreIn 2,zpowers x⁆ = ⁅F.U,zpowers x⁆ := by
  let := h.chosen.elementary
  obtain ⟨K,hKH,hK,hKT,hU,_⟩ := s.component
  have heU := component_core_eq_closure h structural alternatives F s hne K hKH hK hKT hU
  have hxK := point_residual_le_component F s K hKH hK hKT hx
  have hxH := (F.Li_le L 1 hx).2
  have hHQ : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
    F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 F.H))
  have hHK : F.H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp (component_residual F s K hKH hK hKT).1
  have hQU : ⁅F.H.pCoreIn 2,zpowers x⁆ ≤ F.U := by
    rw [heU]
    apply (show ⁅F.H.pCoreIn 2,zpowers x⁆ ≤ K ⊓ F.H.pCoreIn 2 from ?_).trans
      (inf_pCoreIn_le_of_le 2 hKH)
    refine le_inf ?_ (le_normalizer_iff_commutator_le_left.mp ((zpowers_le.mpr hxH).trans hHQ))
    exact (commutator_mono le_rfl (zpowers_le.mpr hxK)).trans
      (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 F.H).trans hHK))
  have hid : ⁅⁅F.H.pCoreIn 2,zpowers x⁆,zpowers x⁆ = ⁅F.H.pCoreIn 2,zpowers x⁆ := by
    rw [zpowers_eq_closure]
    apply commutator_closure_coprime_idempotent (F.H.pCoreIn 2) {x}
      (by rw [← zpowers_eq_closure]; exact (zpowers_le.mpr hxH).trans hHQ)
    rintro a (rfl : a = x)
    rw [hx3]
    obtain ⟨n,hn⟩ := (T.isPGroup'.to_le (point_core_le_sylow F)).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by decide)
  apply le_antisymm (hid.symm.le.trans (commutator_mono hQU le_rfl))
  exact commutator_mono (le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 6) s.core_shape.card) F.U_le_H
    (le_normalizer_conjugateSpanBy V F.H)) le_rfl

/-- The original cubic centralizer supplements [U,X₁] in Q. -/
theorem point_core_cubic_decomposition
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3) :
    F.H.pCoreIn 2 = ⁅F.U,zpowers x⁆ ⊔
      (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) := by
  let := h.chosen.elementary
  have hp := T.isPGroup'.to_le (point_core_le_sylow F)
  let := hp.isNilpotent
  have hn : zpowers x ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
    (zpowers_le.mpr (F.Li_le L 1 hx).2).trans
      (F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 F.H)))
  have hc : Nat.Coprime (Nat.card (zpowers x)) (Nat.card (F.H.pCoreIn 2)) := by
    rw [Nat.card_zpowers,hx3]
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by decide)
  have hd := eq_commutator_sup_centralizer_of_solvable_coprime _ _ hn inferInstance hc
  rw [point_core_cubic_commutator h structural alternatives F s hne x hx hx3] at hd
  exact hd


end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup

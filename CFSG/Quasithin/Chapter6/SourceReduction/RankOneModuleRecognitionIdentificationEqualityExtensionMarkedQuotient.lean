module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionGeneration
public import Theory.SpecificGroups.Alternating.FiveExtensionAction

/-!
# The marked symmetric-five quotient of the equality local group

The normal image of L in M/O₂(M) is A₅, with two-group supplement
provided by M=LT. It is self-centralizing since the quotient has trivial
two-core. If T acted internally, the entire plane Z_S would centralize T,
contradicting its cyclic central omega subgroup. Thus Aut(A₅)=S₅ gives
the quotient equivalence and marks the image of L under that same map.

The quotient is transported to the original Q=O₂(LT). No splitting and
no conclusion about |D| are assumed. The equality-geometry owner retains
the remaining centralizer bound and elementary-four transfer exclusion.
Source: Aschbacher–Smith, proof of 6.2.13, printed pp.687–688.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The cyclic central omega line forces a genuine outer Sylow actor. -/
theorem LocalAnalysis.equality_sylow_not_le_local_core_join
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (horder : orderOf z = 2) :
    ¬ (T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  intro hT
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    rw [← equality_sylow_centralizer_eq_core h611 hnatural]
    exact inf_le_left
  have hLQ : L ≤ normalizer (Q : Set G) :=
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hZC : ZS (T : Subgroup G) L R ≤ centralizer (T : Set G) := by
    intro v hv t ht
    have hprod : t ∈ (L : Set G) * (Q : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right L Q hLQ]
      exact hT ht
    obtain ⟨l, hl, q, hq, rfl⟩ := hprod
    have hlT : l ∈ (T : Subgroup G) := by
      have hh := (T : Subgroup G).mul_mem ht ((T : Subgroup G).inv_mem (hQT hq))
      simpa only [mul_inv_cancel_right] using hh
    have hlv : l * v = v * l := hv.2 l ⟨hlT, hl⟩
    have hqv : q * v = v * q := (local_core_centralizes_layer h611 hq v hv.1).symm
    calc
      (l * q) * v = l * (q * v) := mul_assoc _ _ _
      _ = l * (v * q) := congrArg (l * ·) hqv
      _ = (l * v) * q := (mul_assoc _ _ _).symm
      _ = (v * l) * q := congrArg (· * q) hlv
      _ = v * (l * q) := mul_assoc _ _ _
  have hZ : ZS (T : Subgroup G) L R ≤ centralOmega (T : Subgroup G) := by
    let := h611.ZS_elementary
    intro v hv
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl v
      ⟨h611.ZS_le_T hv, hZC hv⟩ (elemPow_eq_one_of_isElementaryAbelian v hv)
  have hc := card_le_of_le hZ
  rw [(h611.natural_ZS_geometry hnatural).2.1, A.central_omega, Nat.card_zpowers, horder] at hc
  omega

/-- The canonical quotient is symmetric five, provided by its normal A₅ and
an outer actor detected by the central omega line. The generation premise
is supplied by natural-vector transitivity in the source application. -/
theorem LocalAnalysis.equality_marked_maximal_core_quotient
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    (hlocal : M = L ⊔ (T : Subgroup G)) :
    ∃ e : (M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 5),
      (L.subgroupOf M).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))) =
        alternatingGroup (Fin 5) := by
  let π := QuotientGroup.mk' (pCore 2 M)
  let B := L.subgroupOf M
  let K := B.map π
  let S := ((T : Subgroup G).subgroupOf M).map π
  let : B.Normal := h611.L_normal
  let : K.Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have hB : B.IsCComponent := by
    change (L.subgroupOf M).IsCComponent
    rw [hlocal]
    exact h611.local_mem.1.prop.1
  obtain ⟨e₀⟩ := h611.quotient_a5_of_n_eq_two hnatural.1
  let c := subgroupOfEquivOfLe h611.L_le
  let eK : K ≃* alternatingGroup (Fin 5) :=
    (cComponentTwoCoreQuotientEquiv hB).symm.trans
      ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e₀)
  have hgen : K ⊔ S = ⊤ := by
    rw [← Subgroup.map_sup, ← subgroupOf_sup h611.L_le h611.sylow_le, ← hlocal,
      subgroupOf_self, map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype.map π
  have hquot : IsPGroup 2 ((M ⧸ pCore 2 M) ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K S hS hgen
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K := eK.isSimpleGroup
  have hnoncomm : ¬ IsMulCommutative K := by
    intro hc
    have ha : IsMulCommutative (alternatingGroup (Fin 5)) :=
      isMulCommutative_iff.mpr (fun a b => eK.symm.injective (by
        simpa only [map_mul] using (isMulCommutative_iff.mp hc) (eK.symm a) (eK.symm b)))
    have hh := alternatingGroup.isMulCommutative_iff_card_le_three.mp ha
    norm_num at hh
  have hC : centralizer (K : Set (M ⧸ pCore 2 M)) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient K hnoncomm hquot (pCore_quotient_pCore_eq_bot 2)
  have hKtop : K ≠ ⊤ := by
    intro ht
    have hm := congrArg (fun D : Subgroup (M ⧸ pCore 2 M) => (D.comap π).map M.subtype) ht
    change ((B.map π).comap π).map M.subtype =
      ((⊤ : Subgroup (M ⧸ pCore 2 M)).comap π).map M.subtype at hm
    rw [comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
      map_subgroupOf_eq_of_le h611.L_le, comap_top,
      ← MonoidHom.range_eq_map, range_subtype] at hm
    change L ⊔ M.pCoreIn 2 = M at hm
    rw [← A.equality_local_core_eq_maximal_core h611 hnatural hz horder hTH hbranch] at hm
    exact A.equality_sylow_not_le_local_core_join h611 hnatural horder
      (h611.sylow_le.trans_eq hm.symm)
  obtain ⟨t, ht⟩ := SetLike.exists_not_mem_of_ne_top K hKtop
  have hout : (MulAut.conjNormal t : MulAut K) ∉ MulAut.innerSubgroup K := by
    rintro ⟨k, hk⟩
    have hk' : (MulAut.conjNormal (k : M ⧸ pCore 2 M) : MulAut K) =
        MulAut.conjNormal t := by
      rw [MulAut.conjNormal_val]
      exact hk
    have ha : (MulAut.conjNormal ((k : M ⧸ pCore 2 M)⁻¹ * t) : MulAut K) = 1 := by
      rw [map_mul, map_inv, hk', inv_mul_cancel]
    have hc : (k : M ⧸ pCore 2 M)⁻¹ * t ∈ centralizer (K : Set (M ⧸ pCore 2 M)) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      exact ha
    have he : (k : M ⧸ pCore 2 M) = t := by
      rw [hC, mem_bot] at hc
      exact inv_mul_eq_one.mp hc
    exact ht (he ▸ k.property)
  obtain ⟨e, he⟩ := Theory.SpecificGroups.Alternating.FiveExtensionAction.exists_equiv K eK hC t hout
  refine ⟨e, ?_⟩
  rw [← map_map]
  change K.map e.toMonoidHom = alternatingGroup (Fin 5)
  ext a
  constructor
  · rintro ⟨k, hk, rfl⟩
    change e k ∈ alternatingGroup (Fin 5)
    rw [he ⟨k, hk⟩]
    exact (eK ⟨k, hk⟩).property
  · intro ha
    obtain ⟨k, hk⟩ := eK.surjective ⟨a, ha⟩
    exact ⟨k, k.property, (he k).trans (congrArg Subtype.val hk)⟩

/-- The marked symmetric-five quotient uses the original local core and the
same quotient map for the image of L. No splitting is asserted. -/
theorem LocalAnalysis.equality_marked_local_core_quotient
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    let := A.equality_local_core_normal h611 hnatural hz horder hTH hbranch
    ∃ e : (M ⧸ ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M) ≃*
        Equiv.Perm (Fin 5),
      (L.subgroupOf M).map (e.toMonoidHom.comp
        (QuotientGroup.mk' (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M))) =
          alternatingGroup (Fin 5) := by
  let := A.equality_local_core_normal h611 hnatural hz horder hTH hbranch
  obtain ⟨e, he⟩ := A.equality_marked_maximal_core_quotient h611 hnatural hz horder hTH hbranch
    (A.equality_maximal_eq_local h611 hnatural hz horder hTH hbranch)
  have hQ : ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M = pCore 2 M := by
    rw [A.equality_local_core_eq_maximal_core h611 hnatural hz horder hTH hbranch]
    change ((pCore 2 M).map M.subtype).comap M.subtype = pCore 2 M
    exact comap_map_eq_self_of_injective M.subtype_injective _
  let c := QuotientGroup.quotientMulEquivOfEq hQ
  refine ⟨c.trans e, ?_⟩
  have hm : (c.trans e).toMonoidHom.comp
      (QuotientGroup.mk' (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M)) =
      e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M)) := by
    apply MonoidHom.ext
    intro m
    exact congrArg e (QuotientGroup.quotientMulEquivOfEq_mk hQ m)
  rw [hm]
  exact he

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

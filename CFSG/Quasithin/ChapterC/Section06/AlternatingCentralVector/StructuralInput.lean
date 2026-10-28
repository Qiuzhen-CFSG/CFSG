module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.Quotient
public import CFSG.Quasithin.ChapterC.Section06.GeneralFactorizationSource

/-!
# The ordinary A₇ split in the literal C.6.3 quotient

The direct split makes Q/D an image of the elementary block module.
Its Frattini subgroup is therefore trivial. We use exactly the quotient
of K R by C_R(K) that occurs in `c6_3_source_structural_factorization`.
The structural application retains only the separate normalizer-index
and minimum-centralizer-rank hypotheses.

Source: Aschbacher–Smith C.6.3(3)(a,b) and C.6.4, printed pp.167–168.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

omit [Finite G] in
/-- The notation U in the source is the intrinsic block layer in the input. -/
theorem source_module_eq (K : Subgroup G) :
    ⁅(pCore 2 K).map K.subtype, K⁆ = (blockU K).map K.subtype := by
  rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]

/-- The Frattini premise of C.6.3 on its literal quotient by D. -/
theorem Input.source_frattini (d : Input K R S Λ) :
    let D := R ⊓ centralizer (K : Set G)
    let J := K ⊔ R
    letI := c6_3_centralizer_normal K R
      ((d.R_le_S.trans le_sup_right).trans d.normalizes_block)
    frattini (((J.pCoreIn 2).subgroupOf J).map
      (QuotientGroup.mk' (D.subgroupOf J))) = ⊥ := by
  intro D J
  let := c6_3_centralizer_normal K R
    ((d.R_le_S.trans le_sup_right).trans d.normalizes_block)
  let U := (blockU K).map K.subtype
  let f := QuotientGroup.mk' (D.subgroupOf J)
  have hU : U ≤ J := (map_subtype_le _).trans le_sup_left
  have hD : D ≤ J := inf_le_left.trans le_sup_right
  have hsplit : J.pCoreIn 2 = D ⊔ U := by
    change (K ⊔ R).pCoreIn 2 = _
    rw [d.block_sup_R]
    exact d.core_direct_split.1
  have hm : ((J.pCoreIn 2).subgroupOf J).map f = (U.subgroupOf J).map f := by
    rw [hsplit, subgroupOf_sup hD hU, Subgroup.map_sup,
      show (D.subgroupOf J).map f = ⊥ from
        (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' _).ge, bot_sup_eq]
  change frattini (((J.pCoreIn 2).subgroupOf J).map f) = ⊥
  rw [hm]
  let : IsElementaryAbelian 2 U := d.block.2.1.elementary.map K.subtype
  let : IsElementaryAbelian 2 (U.subgroupOf J) := IsElementaryAbelian.subgroupOf hU
  let : IsElementaryAbelian 2 ((U.subgroupOf J).map f) := IsElementaryAbelian.map f
  let : Fact (IsPGroup 2 ((U.subgroupOf J).map f)) :=
    ⟨IsElementaryAbelian.isPGroup 2 _⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

/-- The quotient part of C.6.3(b), with its original core and normality instance. -/
theorem Input.source_quotient (d : Input K R S Λ) :
    letI := c6_3_two_core_normal K R
    IsElementaryAbelian 2
        (R ⧸ (((pCore 2 (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype).subgroupOf R)) ∧
      Group.rank (R ⧸ (((pCore 2 (K ⊔ R : Subgroup G)).map
        (K ⊔ R).subtype).subgroupOf R)) = 1 := by
  let := c6_3_two_core_normal K R
  let := d.core_normal_in_R
  have heq : (((pCore 2 (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype).subgroupOf R) =
      ((K ⊔ S).pCoreIn 2).subgroupOf R :=
    congrArg (fun H : Subgroup G => (H.pCoreIn 2).subgroupOf R) d.block_sup_R
  let e := QuotientGroup.quotientMulEquivOfEq heq
  let := d.quotient_elementary_rank_one.1
  exact ⟨IsElementaryAbelian.of_injective e.toMonoidHom e.injective,
    (Group.rank_congr e).trans d.quotient_elementary_rank_one.2⟩

/-- Application to C.6.3: the core, quotient and Frattini premises are
proved above. Only the geometric minimum and the escape index remain. -/
theorem Input.structural_factorization (d : Input K R S Λ)
    (hi : (S ⊓ Λ).relIndex (Λ ⊓ normalizer (R : Set G)) = 2)
    (hmin : letI := d.block.2.1.elementary.map K.subtype
      centralizerRankMinimum R ((blockU K).map K.subtype) = 1) :
    let U := (blockU K).map K.subtype
    let Q := (K ⊔ S).pCoreIn 2
    let D := R ⊓ centralizer (K : Set G)
    ∃ x ∈ (Λ ⊓ normalizer (R : Set G)) ⊔ S,
      ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q ∧
      R = U.map (MulAut.conj x⁻¹ : G →* G) ⊔ Q ∧
      Q = U ⊔ (Q ⊓ centralizer (U.map (MulAut.conj x⁻¹ : G →* G) : Set G)) ∧
      R = (U ⊔ U.map (MulAut.conj x⁻¹ : G →* G)) ⊔
        (R ⊓ centralizer ((U ⊔ U.map (MulAut.conj x⁻¹ : G →* G) : Subgroup G) : Set G)) ∧
      D ⊓ D.map (MulAut.conj x⁻¹ : G →* G) = ⊥ ∧
      frattini D = ⊥ ∧ IsElementaryAbelian 2 Q ∧
      R = Q ⊔ Q.map (MulAut.conj x⁻¹ : G →* G) := by
  let : IsElementaryAbelian 2 ((blockU K).map K.subtype) := d.block.2.1.elementary.map K.subtype
  let : IsElementaryAbelian 2 (⁅(pCore 2 K).map K.subtype, K⁆ : Subgroup G) := by
    rw [source_module_eq]
    infer_instance
  have hres : twoResidualAmbient K = K := by
    have hr : twoResidualSubgroup K = pResidual 2 K := by
      unfold twoResidualSubgroup pResidual
      congr 1
      ext N
      constructor
      · rintro ⟨hn,n,hc⟩
        let : N.Normal := hn
        exact ⟨hn,IsPGroup.of_card hc⟩
      · rintro ⟨hn,hp⟩
        exact ⟨hn,hp.exists_card_eq⟩
    rw [twoResidualAmbient, hr, d.block.2.1.residual_eq_top,
      ← MonoidHom.range_eq_map, range_subtype]
  have hU : ⁅(pCore 2 K).map K.subtype, K⁆ ≠ ⊥ := by
    rw [source_module_eq]
    intro he
    exact d.block.2.1.blockU_ne_bot ((map_injective K.subtype_injective)
      (he.trans (map_bot K.subtype).symm))
  have hQR : (pCore 2 (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype ≤ R := by
    rw [d.block_sup_R]
    exact d.core_le
  have hno (W : Subgroup G) (hne : W ≠ ⊥) (hWR : W ≤ R)
      (hn : (W.subgroupOf (K ⊔ S)).Normal) :
      ¬ Λ ⊓ normalizer (R : Set G) ≤ Λ ⊓ normalizer (W : Set G) :=
    d.no_normal_subgroup hne hWR
      ((normal_subgroupOf_iff_le_normalizer
        (hWR.trans (d.R_le_S.trans le_sup_right))).mp hn)
  have hQ : (pCore 2 (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype =
      R ⊓ centralizer ((⁅(pCore 2 K).map K.subtype,K⁆ : Subgroup G) : Set G) := by
    rw [source_module_eq, d.block_sup_R]
    exact d.core_eq_centralizer
  let : (((K ⊔ R).pCoreIn 2).subgroupOf R).Normal := c6_3_two_core_normal K R
  have hrank : Group.rank (R ⧸ ((K ⊔ R).pCoreIn 2).subgroupOf R) =
      centralizerRankMinimum R (⁅(pCore 2 K).map K.subtype,K⁆) := by
    refine d.source_quotient.2.trans ?_
    simpa only [source_module_eq] using hmin.symm
  obtain ⟨x,hx,he,hR,hQ',hfull,_,hD,hphi,hE,hQQ⟩ :=
    c6_3_source_structural_factorization K R S Λ hres hU hQR d.R_le_S
      (normal_subgroupOf_of_le_normalizer d.S_normalizes_R) d.S_two
      d.S_normalizes_Λ (le_sup_right.trans d.normalizes_block) hno hi
      hQ d.source_quotient.1 hrank d.source_frattini
  have hcore : (pCore 2 (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype =
      (K ⊔ S).pCoreIn 2 := congrArg (pCoreIn 2) d.block_sup_R
  exact ⟨x,hx,by simpa only [source_module_eq, hcore] using he,
    by simpa only [source_module_eq, hcore] using hR,
    by simpa only [source_module_eq, hcore] using hQ',
    by simpa only [source_module_eq] using hfull, hD, hphi,
    by
      let := hE
      let e := MulEquiv.subgroupCongr hcore
      exact IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective,
    by simpa only [hcore] using hQQ⟩

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector

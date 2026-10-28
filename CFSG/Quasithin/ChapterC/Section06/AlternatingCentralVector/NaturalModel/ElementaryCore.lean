module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.NaturalModel.Factorization
public import Theory.GroupTheory.PGroup.NormalIndexTwoStep

/-!
# The elementary core from an actual index-two escape

The finite two-group normalizer condition gives R < NΛ(R). Choose an
index-two step X₁ above R inside that normalizer, and apply C.6.3 with
(R,X₁) in the roles of (T,Λ). The original normalizer obstruction remains
valid since K R = K S. This proves the elementary core, the disjointness
D ∩ Dˣ = 1, and R = Q Qˣ without assuming the index of NΛ(R).

Source: Aschbacher–Smith C.6.4, first half of the proof, printed p.168.
The subsequent maximum-elementary-family and dihedral endgame remain separate.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
open Stellmacher
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

private theorem index_two_step (d : Input K R S Λ) :
    ∃ X₁ : Subgroup G, R ≤ X₁ ∧ X₁ ≤ Λ ⊓ normalizer (R : Set G) ∧ R.relIndex X₁ = 2 := by
  let X := Λ ⊓ normalizer (R : Set G)
  let R₀ := R.subgroupOf X
  have hRX : R ≤ X := d.lt_normalizer.le
  let : R₀.Normal := normal_subgroupOf_of_le_normalizer inf_le_right
  have hp : IsPGroup 2 X := d.Λ_two.to_le inf_le_left
  have hproper : R₀ < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => d.lt_normalizer.not_ge (subgroupOf_eq_top.mp he))
  obtain ⟨Y,_,hRY,_,hi⟩ := exists_normal_index_two_step X hp R₀ ⊤ hproper
  have hmap : R₀.map X.subtype = R := map_subgroupOf_eq_of_le hRX
  refine ⟨Y.map X.subtype, ?_,map_subtype_le _,?_⟩
  · rw [← hmap]
    exact map_mono hRY
  · have hh := relIndex_map_map_of_injective R₀ Y X.subtype_injective
    rw [hmap,hi] at hh
    exact hh

/-- The elementary-core and disjoint-centralizer conclusions are obtained on
an actual index-two step inside NΛ(R). The index of NΛ(R) itself is not assumed. -/
theorem Input.exists_elementary_factorization (d : Input K R S Λ) :
    let U := (blockU K).map K.subtype
    let Q := (K ⊔ S).pCoreIn 2
    let D := R ⊓ centralizer (K : Set G)
    ∃ x ∈ Λ ⊓ normalizer (R : Set G),
      ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q ∧
      R = U.map (MulAut.conj x⁻¹ : G →* G) ⊔ Q ∧
      Q = U ⊔ (Q ⊓ centralizer (U.map (MulAut.conj x⁻¹ : G →* G) : Set G)) ∧
      D ⊓ D.map (MulAut.conj x⁻¹ : G →* G) = ⊥ ∧
      frattini D = ⊥ ∧ IsElementaryAbelian 2 Q ∧
      R = Q ⊔ Q.map (MulAut.conj x⁻¹ : G →* G) := by
  obtain ⟨X₁,hRX,hXΛ,hi⟩ := index_two_step d
  have hXn : X₁ ≤ normalizer (R : Set G) := hXΛ.trans inf_le_right
  have hXproper : R < X₁ := lt_of_le_of_ne hRX (by intro he; simp [← he] at hi)
  let := d.block.2.1.elementary.map K.subtype
  let : IsElementaryAbelian 2 (⁅(pCore 2 K).map K.subtype,K⁆ : Subgroup G) := by
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
    rw [twoResidualAmbient,hr,d.block.2.1.residual_eq_top,
      ← MonoidHom.range_eq_map,range_subtype]
  have hU : ⁅(pCore 2 K).map K.subtype,K⁆ ≠ ⊥ := by
    rw [source_module_eq]
    intro he
    exact d.block.2.1.blockU_ne_bot ((map_injective K.subtype_injective)
      (he.trans (map_bot K.subtype).symm))
  have hcore : (pCore 2 (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype =
      (K ⊔ S).pCoreIn 2 := congrArg (pCoreIn 2) d.block_sup_R
  have hQR : (pCore 2 (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype ≤ R := hcore ▸ d.core_le
  have hno (W : Subgroup G) (hne : W ≠ ⊥) (hWR : W ≤ R)
      (hn : (W.subgroupOf (K ⊔ R)).Normal) :
      ¬ X₁ ⊓ normalizer (R : Set G) ≤ X₁ ⊓ normalizer (W : Set G) := by
    have hHn : K ⊔ S ≤ normalizer (W : Set G) := by
      rw [← d.block_sup_R]
      exact (normal_subgroupOf_iff_le_normalizer (hWR.trans le_sup_right)).mp hn
    intro hh
    apply hXproper.not_ge
    intro x hx
    have hxW := hh ⟨hx,hXn hx⟩
    rw [← d.control W hne hWR hHn]
    exact ⟨(hXΛ hx).1,hxW.2⟩
  have hi' : (R ⊓ X₁).relIndex (X₁ ⊓ normalizer (R : Set G)) = 2 := by
    rwa [inf_eq_left.mpr hRX,inf_eq_left.mpr hXn]
  have hQ : (pCore 2 (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype =
      R ⊓ centralizer ((⁅(pCore 2 K).map K.subtype,K⁆ : Subgroup G) : Set G) := by
    rw [hcore,source_module_eq]
    exact d.core_eq_centralizer
  let : (((K ⊔ R).pCoreIn 2).subgroupOf R).Normal := c6_3_two_core_normal K R
  have hrank : Group.rank (R ⧸ ((K ⊔ R).pCoreIn 2).subgroupOf R) =
      centralizerRankMinimum R (⁅(pCore 2 K).map K.subtype,K⁆) := by
    refine d.source_quotient.2.trans ?_
    simpa only [source_module_eq] using d.centralizer_rank_minimum.symm
  obtain ⟨x,hx,he,hR,hQ',_,_,hD,hphi,hE,hQQ⟩ :=
    c6_3_source_structural_factorization K R R X₁ hres hU hQR le_rfl
      (normal_subgroupOf_of_le_normalizer R.le_normalizer) (d.S_two.to_le d.R_le_S)
      (hRX.trans X₁.le_normalizer)
      ((d.R_le_S.trans le_sup_right).trans d.normalizes_block)
      hno hi' hQ d.source_quotient.1 hrank d.source_frattini
  refine ⟨x,hXΛ ((sup_le inf_le_left hRX) hx),?_,?_,?_,hD,hphi,?_,?_⟩
  · simpa only [source_module_eq,hcore] using he
  · simpa only [source_module_eq,hcore] using hR
  · simpa only [source_module_eq,hcore] using hQ'
  · let := hE
    let e := MulEquiv.subgroupCongr hcore
    exact IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  · simpa only [hcore] using hQQ

/-- In the original C.6.4 configuration the entire two-core is elementary. -/
theorem Input.core_elementary (d : Input K R S Λ) :
    IsElementaryAbelian 2 ((K ⊔ S).pCoreIn 2) := by
  obtain ⟨_,_,_,_,_,_,_,hE,_⟩ := d.exists_elementary_factorization
  exact hE

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector

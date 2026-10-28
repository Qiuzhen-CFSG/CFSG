module
public import Theory.Representation.RankOne.QuadraticRecognition.SmallProjectiveOvergroups
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveUnitaryEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveUnitaryBorel
public import Theory.Representation.RankOne.QuadraticRecognition.Generation
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PrimeRankHom
public import Theory.SpecificGroups.SU3.EvenTwoRank

/-!
# Faithful sections of the original small projective enlargement

For an original PSU₃(2) quotient, the enlarged endpoint meets the full
Borel precisely in its two-core. The rank-one overgroup alternative then
forces every nontrivial Sylow-fixed-generated representation of the actual
enlarged core quotient to be faithful. The original starred image has
2-rank one and index at most two, giving 2-rank at most two for that quotient. Its normal quaternion-by-nine
subgroup also supplies the strict cubic-ratio bound.

These statements retain the possible order-144 enlargement. They apply to
the replacement section in SmallProjectiveReplacement without assuming an
enlarged PSU₃(2) marking or excluding its outer actors.
Source: DGS, Groups and Graphs (1985), 6.1 and 6.4--6.5, pp.118--122,
with the fixed-space-generation requirement of corrected 5.12.
-/

public noncomputable section
open scoped Pointwise
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Representation Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}

/-- The full Borel meets the enlargement precisely in its original two-core. -/
theorem small_projective_enlargement_inf_borel (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hm : ClassicalGroup.IsPSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 2) :
    localEnlargement d ⊓ B = B.pCoreIn 2 := by
  let := d.finite_P
  let : Finite B := Finite.of_injective (inclusion (le_sup_right.trans d.supplement.le))
    (inclusion_injective _)
  have hR := pCoreIn_le 2 B
  have hT : (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ B.pCoreIn 2 :=
    pGroup_le_core_of_core_sylow B _ (source_star_sylow_le_borel d) (d.sylow.isPGroup'.map _) hB
  apply le_antisymm ?_ (le_inf le_sup_right hR)
  intro x hx
  have hp : x ∈ (B.pCoreIn 2 : Set G) * (d.Pstar : Set G) :=
    localEnlargement_product d ▸ hx.1
  obtain ⟨r,hr,y,hy,rfl⟩ := hp
  have hyB : y ∈ B := by
    simpa only [inv_mul_cancel_left] using B.mul_mem (B.inv_mem (hR hr)) hx.2
  have hyR : y ∈ B.pCoreIn 2 := hT
    ((source_star_borel_eq_sylow_of_small_projective_unitary d hm) ▸ ⟨hy,hyB⟩)
  exact (B.pCoreIn 2).mul_mem hr hyR

private theorem trivial_of_kernel_sup_fixed (D W : Type*) [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (T : Subgroup D)
    (hg : GeneratedByFixedSpace σ T) (hsup : σ.ker ⊔ T = ⊤) : σ = 1 := by
  have hR : fixedSpace σ σ.ker = ⊤ := by
    apply top_unique
    intro w _ a
    change σ a w = w
    rw [show σ a = 1 from a.property]
    rfl
  have hfix : fixedSpace σ ⊤ = fixedSpace σ T := by
    have he := σ.invariants_comp_sup σ.ker T
    change fixedSpace σ (σ.ker ⊔ T) = fixedSpace σ σ.ker ⊓ fixedSpace σ T at he
    rwa [hsup,hR,top_inf_eq] at he
  have hspan : (⨆ g : D, (fixedSpace σ T).map (σ g)) ≤ fixedSpace σ ⊤ := by
    apply iSup_le
    rintro g _ ⟨v,hv,rfl⟩
    have hv' : v ∈ fixedSpace σ ⊤ := hfix.symm ▸ hv
    rw [show σ g v = v from hv' ⟨g,mem_top _⟩]
    exact hv'
  have htop : fixedSpace σ ⊤ = ⊤ := top_unique (hg ▸ hspan)
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro w
  exact (show w ∈ fixedSpace σ ⊤ from htop.symm ▸ Submodule.mem_top) ⟨g,mem_top _⟩

theorem small_projective_enlargement_fixed_generated_faithful
    (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype ≤ B)
    (hm : ClassicalGroup.IsPSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (localEnlargement d ⧸ pCore 2 (localEnlargement d)) W)
    (hg : ∀ T : Sylow 2 (localEnlargement d ⧸ pCore 2 (localEnlargement d)),
      GeneratedByFixedSpace σ T) (hnt : σ ≠ 1) : Function.Injective σ := by
  let M := localEnlargement d
  let R := B.pCoreIn 2
  let D := M ⧸ pCore 2 M
  let q := QuotientGroup.mk' (pCore 2 M)
  let := d.finite_P
  let : Finite M := Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  let : Finite B := Finite.of_injective (inclusion (le_sup_right.trans d.supplement.le)) (inclusion_injective _)
  have hRM : R ≤ M := le_sup_right
  have hRB : R ≤ B := pCoreIn_le 2 B
  have hRP : R ≤ P := hRM.trans (localEnlargement_le d)
  obtain ⟨T,hT⟩ := hS
  have hTR : (T : Subgroup P).map P.subtype = R :=
    sylow_image_eq_edge_core P B (le_sup_right.trans d.supplement.le) hB T hT
  let TM := T.subtype (show (T : Subgroup P) ≤ M.subgroupOf P from fun t ht =>
    hRM (hTR ▸ mem_map_of_mem P.subtype ht))
  let f : M.subgroupOf P ≃* M := subgroupOfEquivOfLe (localEnlargement_le d)
  let U := TM.mapSurjective (f := f.toMonoidHom) f.surjective
  have hUR : (U : Subgroup M) = R.subgroupOf M := by
    ext m
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hTR ▸ mem_map_of_mem P.subtype hx
    · intro hm
      obtain ⟨t,ht,he⟩ := hTR.symm ▸ hm
      exact ⟨⟨t,by
        change (t : G) ∈ M
        change (t : G) = (m : G) at he
        rw [he]
        exact m.property⟩,ht,Subtype.ext he⟩
  let V := quotientSylow U
  have hV : (V : Subgroup D) = (R.subgroupOf M).map q := by
    change (U : Subgroup M).map q = _
    rw [hUR]
  let K := σ.ker.comap q
  let H := K.map M.subtype
  have hHM : H ≤ M := map_subtype_le _
  have htop : H ⊔ R ≠ M := by
    intro he
    have hh := congrArg (fun N : Subgroup G => N.subgroupOf M) he
    rw [subgroupOf_sup hHM hRM,subgroupOf_self] at hh
    change (K.map M.subtype).comap M.subtype ⊔ R.subgroupOf M = ⊤ at hh
    rw [comap_map_eq_self_of_injective M.subtype_injective] at hh
    have hh' := congrArg (Subgroup.map q) hh
    rw [Subgroup.map_sup,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at hh'
    exact hnt (trivial_of_kernel_sup_fixed D W σ V (hg V) (by rwa [hV]))
  have hTB : (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ R :=
    pGroup_le_core_of_core_sylow B _ (source_star_sylow_le_borel d) (d.sylow.isPGroup'.map _) hB
  have hHB : H ≤ B := by
    rcases source_overgroup_star_or_borel d (H ⊔ R)
      ((sup_le hHM hRM).trans (localEnlargement_le d)) (hTB.trans le_sup_right) with hs | hb
    · exact (htop (le_antisymm (sup_le hHM hRM) (sup_le hs le_sup_right))).elim
    · exact le_sup_left.trans hb
  have hKR : K ≤ R.subgroupOf M := by
    intro x hx
    exact (small_projective_enlargement_inf_borel d hB hm).le
      ⟨x.property,hHB (mem_map_of_mem M.subtype hx)⟩
  have hKp : IsPGroup 2 σ.ker := by
    have hp := ((isPGroup_pCoreIn 2 B).comap_subtype.to_le hKR).map q
    change IsPGroup 2 ((σ.ker.comap q).map q) at hp
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hp
  have hk : σ.ker ≤ pCore 2 D := le_sSup ⟨inferInstance,hKp⟩
  exact σ.ker_eq_bot_iff.mp (bot_unique
    (hk.trans (pCore_quotient_pCore_eq_bot (G := M) 2).le))


open BenderSuzuki.MatrixGroups in
/-- The possible outer enlargement raises the two-rank by at most one. -/
theorem small_projective_enlargement_twoRank (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hm : ClassicalGroup.IsPSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 2) :
    primeRank 2 (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≤ 2 := by
  obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  let M := localEnlargement d
  let D := M ⧸ pCore 2 M
  let C := d.Pstar.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let I := C.map q
  let := d.finite_P
  let : Finite M := Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective e.symm e.symm.injective
  let : C.Normal := normal_subgroupOf_of_le_normalizer ((localEnlargement_le d).trans
    ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal))
  let f : C ≃* d.Pstar := subgroupOfEquivOfLe (show d.Pstar ≤ M from le_sup_left)
  let g : I ≃* ProjectiveSpecialUnitaryMatrixGroup J := (coreQuotientEquivImage 2 C).symm.trans
    ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e)
  have hI : Nat.card I = 72 := (Nat.card_congr g.toEquiv).trans
    (HermitianForm.FixedFieldTwo.card_projective J hc hconj)
  have hD : Nat.card D ≤ 144 := by
    rcases localEnlargement_small_projective_alternatives d hB J hc hconj e with he | he
    · let f := MulEquiv.subgroupCongr he
      have hh := Nat.card_congr ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e).toEquiv
      rw [HermitianForm.FixedFieldTwo.card_projective J hc hconj] at hh
      exact hh.le.trans (by decide)
    · exact he.le
  have hi : I.index ≤ 2^1 := by
    have hh := I.card_mul_index
    rw [hI] at hh
    change Nat.card D ≤ 144 at hD
    norm_num only [pow_one]
    nlinarith
  have hr : primeRank 2 I ≤ 1 := by
    rw [primeRank_equiv 2 g]
    exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide)
      (by simpa using hc) (by simpa using hconj)).le
  exact (primeRank_le_add_of_index_le I hi).trans (by omega)

open BenderSuzuki.MatrixGroups in
/-- The actual enlargement has strict cubic ratio, including the order-144 alternative. -/
theorem small_projective_enlargement_cubic_bound (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hm : ClassicalGroup.IsPSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (localEnlargement d ⧸ pCore 2 (localEnlargement d)) W)
    (hf : Function.Injective σ) : 2 < cubicRatio σ := by
  obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  let M := localEnlargement d
  let D := M ⧸ pCore 2 M
  let C := d.Pstar.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let I := C.map q
  let := d.finite_P
  let : Finite M := Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective e.symm e.symm.injective
  let : C.Normal := normal_subgroupOf_of_le_normalizer ((localEnlargement_le d).trans
    ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal))
  let f : C ≃* d.Pstar := subgroupOfEquivOfLe (show d.Pstar ≤ M from le_sup_left)
  let g : I ≃* ProjectiveSpecialUnitaryMatrixGroup J := (coreQuotientEquivImage 2 C).symm.trans
    ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e)
  have hD : Nat.card D = 72 ∨ Nat.card D = 144 := by
    rcases localEnlargement_small_projective_alternatives d hB J hc hconj e with he | he
    · let f := MulEquiv.subgroupCongr he
      have hh := Nat.card_congr ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e).toEquiv
      exact Or.inl (hh.trans (HermitianForm.FixedFieldTwo.card_projective J hc hconj))
    · exact Or.inr he
  let : I.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  exact psu3_two_normal_overgroup_cubic_bound J hc hconj I g hD
    (pCore_quotient_pCore_eq_bot (G := M) 2) σ hf

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem original_small_projective_section_inputs (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2) :
    let hh := SuzukiContainment.reduced_hypothesis h
    (∃ T : Sylow 2 (commonBorel L (SuzukiContainment.reducedSylow L S)),
      (T : Subgroup _) = pCore 2 (commonBorel L (SuzukiContainment.reducedSylow L S))) ∧
    (∃ T : Sylow 2 (parabolic L (SuzukiContainment.reducedSylow L S) i),
      (T : Subgroup _).map (parabolic L (SuzukiContainment.reducedSylow L S) i).subtype ≤
        commonBorel L (SuzukiContainment.reducedSylow L S)) ∧
    ClassicalGroup.IsPSU ((hh.starredLocalRankOneData i).Pstar ⧸
      pCore 2 (hh.starredLocalRankOneData i).Pstar) 3 2 := by
  let hh := SuzukiContainment.reduced_hypothesis h
  refine ⟨?_,?_,?_⟩
  · apply f11_borel_core_sylow hh
    exact (normal_subgroupOf_iff_le_normalizer
      (show SuzukiContainment.reducedSylow L S ≤ commonBorel L (SuzukiContainment.reducedSylow L S)
        from le_sup_right)).mp (SuzukiContainment.reduced_sylow_normal h)
  · obtain ⟨T,hT⟩ := hh.sylow_parabolic i
    exact ⟨T, hT.le.trans le_sup_right⟩
  · obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := hm
    exact ⟨F,hF,hfin,J,hc,hconj,⟨(hh.starredQuotientEquiv i).symm.trans e⟩⟩

/-- Faithfulness on the literal original enlarged quotient, including its possible order-144 branch. -/
theorem original_small_projective_enlargement_faithful (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) W)
    (hg : ∀ T : Sylow 2 (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)),
      GeneratedByFixedSpace σ T) (hnt : σ ≠ 1) : Function.Injective σ := by
  obtain ⟨hB,hS,hm'⟩ := original_small_projective_section_inputs h i hm
  have ht := small_projective_enlargement_fixed_generated_faithful
    ((SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i) hB hS hm' (W := W)
  rw [reduced_localEnlargement_eq h i] at ht
  exact ht σ hg hnt

/-- The actual original enlarged quotient has two-rank at most two. -/
theorem original_small_projective_enlargement_twoRank (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2) :
    primeRank 2 (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ≤ 2 := by
  obtain ⟨hB,_,hm'⟩ := original_small_projective_section_inputs h i hm
  have hr := small_projective_enlargement_twoRank
    ((SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i) hB hm'
  rwa [reduced_localEnlargement_eq h i] at hr

/-- Strict cubic ratio on the literal original enlarged quotient; no order-144 exclusion is required. -/
theorem original_small_projective_enlargement_cubic_bound (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) W)
    (hf : Function.Injective σ) : 2 < cubicRatio σ := by
  obtain ⟨hB,_,hm'⟩ := original_small_projective_section_inputs h i hm
  have hb := small_projective_enlargement_cubic_bound
    ((SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i) hB hm' (W := W)
  rw [reduced_localEnlargement_eq h i] at hb
  exact hb σ hf
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85

module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.Control
public import Theory.Representation.BinaryAlternatingSevenControl.PointStabilizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Ambient

/-!
# Exceptional A₇ seed centralizers and two-subgroup control

In a normal exceptional A₇ block, the Sylow omega-center splits over the
intrinsic four-dimensional layer. Thus the fixed-line centralizer fixes
every original central seed. Its image is a maximal subgroup of index 15,
so any proper component overgroup of the seed centralizer equals it.

The fixed-line stabilizer is the actual GL₃(2), with trivial two-core.
Consequently a two-subgroup of the same Sylow normalized by the marked
intersection centralizes the whole block layer. This additional control
excludes the exceptional row in the original Chapter 15 application using
the actual radical, without assuming the separate C.2.7 index-35 clause.

Source: Aschbacher--Smith C.1.23(2) and 15.1.20(2b), printed pp.130,1095.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
variable {G : Type*} [Group G] [Finite G]

theorem seed_centralizer_control
    (L : Subgroup G) [L.Normal] (hL : IsBlock L) (hm : IsExceptionalA7Block L)
    (T : Sylow 2 G)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (Z : Subgroup G) (hZ : Z ≤ omegaOneCenterAmbient (T : Subgroup G))
    (J : Subgroup L) (hJ : J ≠ ⊤)
    (hCJ : (centralizer (Z : Set G)).comap L.subtype ≤ J) :
    J = (centralizer (Z : Set G)).comap L.subtype ∧ J.index = 15 ∧
      ∀ B : Subgroup G, IsPGroup 2 B → B ≤ (T : Subgroup G) →
        J.map L.subtype ≤ normalizer (B : Set G) →
          B ≤ centralizer ((blockU L).map L.subtype : Set G) := by
  let U := (blockU L).map L.subtype
  let : U.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    exact (show (⊤ : Subgroup G) ≤ normalizer (L : Set G) from le_normalizer_of_normal).trans
      (normalizer_le_normalizer_characteristic_image L (blockU L))
  let := hm.1.elementary.map L.subtype
  let H := G ⧸ centralizer (U : Set G)
  let q : G →* H := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = centralizer (U : Set G) := QuotientGroup.ker_mk' _
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective U q hq hk
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := ambient_finrank L hm
  obtain ⟨a⟩ := image_is_a7 L hm q hk
  let : (L.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have hN : L.map q = ⊤ := BinaryAlternatingSevenControl.normal_alternatingSeven_eq_top ρ hf hd (L.map q) a
  let e : H ≃* alternatingGroup (Fin 7) :=
    ((Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).symm.trans
      (MulEquiv.subgroupCongr hN).symm).trans a
  let r : G →* alternatingGroup (Fin 7) := e.toMonoidHom.comp q
  have hr : Function.Surjective r := e.surjective.comp hq
  have hkr : r.ker = centralizer (U : Set G) :=
    (MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective).trans hk
  have hLr : L.map r = ⊤ := by
    rw [show r = e.toMonoidHom.comp q from rfl, ← map_map, hN,
      map_top_of_surjective _ e.surjective]
  let σ := NormalElementaryQuotient.representation U r hr hkr
  have hσ : Function.Injective σ := NormalElementaryQuotient.representation_injective U r hr hkr
  let R := T.mapSurjective hr
  let C := subspaceKernel σ (fixedSpace σ R) ⊤
  let f := r.comp L.subtype
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨l,hl,he⟩ : x ∈ L.map r := hLr ▸ mem_top x
    exact ⟨⟨l,hl⟩,he⟩
  have hUT : U ≤ (T : Subgroup G) :=
    ((map_mono blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hL.subnormal)).trans
      (pCore_isPGroup.le_sylow_of_normal T)
  have hfix : U ⊓ centralizer ((T : Subgroup G) : Set G) =
      U ⊓ omegaOneCenterAmbient (T : Subgroup G) := by
    apply le_antisymm
    · intro u hu
      exact ⟨hu.1, (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨hUT hu.1, elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu.1, hu.2⟩⟩
    · intro u hu
      exact ⟨hu.1, ((mem_omegaOneCenterAmbient_iff _ _).mp hu.2).2.2⟩
  have hpre : C.comap f =
      (centralizer (U ⊓ omegaOneCenterAmbient (T : Subgroup G) : Set G)).comap L.subtype := by
    ext l
    constructor
    · intro hl u hu
      have hv : (Additive.ofMul ⟨u,hu.1⟩ : Additive U) ∈ fixedSpace σ R := by
        apply (NormalElementaryQuotient.mem_fixedSpace_image U r hr hkr (T : Subgroup G) _).mpr
        exact ((mem_omegaOneCenterAmbient_iff _ _).mp hu.2).2.2
      have he := congrArg (fun w : Additive U => (w.toMul : G)) (hl.2 _ hv)
      dsimp only [σ,f,MonoidHom.comp_apply] at he
      rw [NormalElementaryQuotient.representation_apply] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hl
      refine ⟨mem_top _,fun v hv => ?_⟩
      have hv' := (NormalElementaryQuotient.mem_fixedSpace_image U r hr hkr (T : Subgroup G) v).mp hv
      apply Additive.toMul.injective
      apply Subtype.ext
      dsimp only [σ,f,MonoidHom.comp_apply]
      rw [NormalElementaryQuotient.representation_apply]
      have hvZ : (v.toMul : G) ∈ (U ⊓ omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) := by
        rw [←hfix]
        exact ⟨v.toMul.property,hv'⟩
      have hc := hl v.toMul hvZ
      rw [←hc,mul_inv_cancel_right]
  have hCZ : C.comap f ≤ (centralizer (Z : Set G)).comap L.subtype := by
    rw [hpre]
    intro l hl
    exact (centralizer_le hZ)
      (fixed_line_centralizer_le L hL hm T le_normalizer_of_normal hchar ⟨l.property,hl⟩)
  have hc : IsCoatom (C.comap f) := isCoatom_comap_of_surjective hfs
    (BinaryAlternatingSevenControl.sylow_fixedKernel_coatom σ hσ hd R)
  have he : J = C.comap f := (hc.le_iff_eq hJ).mp (hCZ.trans hCJ)
  refine ⟨le_antisymm ?_ hCJ,?_,?_⟩
  · rw [he]; exact hCZ
  · rw [he,index_comap_of_surjective _ hfs]
    exact BinaryAlternatingSevenControl.sylow_fixedKernel_index σ hσ hd R

  · intro B hB hBT hn
    have hRC : (R : Subgroup (alternatingGroup (Fin 7))) ≤ C := by
      intro g hg
      exact ⟨mem_top _,fun v hv => hv ⟨g,hg⟩⟩
    have hBC : B.map r ≤ C := (map_mono hBT).trans hRC
    have hJC : J.map f = C := by
      rw [he,map_comap_eq_self_of_surjective hfs]
    have hnorm : C ≤ normalizer (B.map r : Set (alternatingGroup (Fin 7))) := by
      rw [←hJC]
      intro x hx
      obtain ⟨l,hl,rfl⟩ := hx
      exact B.le_normalizer_map r (mem_map_of_mem r (hn (mem_map_of_mem L.subtype hl)))
    obtain ⟨v,hv,hvR,hunique⟩ := BinaryAlternatingSevenControl.sylow_fixed_line σ hσ hd R
    have hline : fixedSpace σ R = Submodule.span (ZMod 2) {v} := by
      apply le_antisymm
      · intro w hw
        rcases hunique w hw with rfl | rfl
        · exact Submodule.zero_mem _
        · exact Submodule.subset_span (by simp)
      · exact Submodule.span_le.mpr (by simpa using hvR)
    have hCeq : C = BinaryAlternatingSevenControl.pointStabilizer σ v := by
      dsimp only [C,BinaryAlternatingSevenControl.pointStabilizer]
      rw [hline]
    let ec : C ≃* Matrix.PSL3Two.PSL := (MulEquiv.subgroupCongr hCeq).trans
      (BinaryAlternatingSevenControl.pointStabilizerEquivPSL σ hσ hd hv)
    have hcore : pCore 2 C = ⊥ := by
      apply map_injective (f := ec.toMonoidHom) ec.injective
      rw [pCore_map_iso,Matrix.PSL3Two.pCore_two_PSL_eq_bot,Subgroup.map_bot]
    let : ((B.map r).subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hnorm
    have hsub : (B.map r).subgroupOf C ≤ pCore 2 C :=
      le_sSup ⟨inferInstance,(hB.map r).comap_subtype⟩
    intro b hb
    have hh := hsub (show (⟨r b,hBC (mem_map_of_mem r hb)⟩ : C) ∈
        (B.map r).subgroupOf C from mem_map_of_mem r hb)
    rw [hcore] at hh
    have hz : r b = 1 := congrArg Subtype.val hh
    exact hkr ▸ (show b ∈ r.ker from hz)

end CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl

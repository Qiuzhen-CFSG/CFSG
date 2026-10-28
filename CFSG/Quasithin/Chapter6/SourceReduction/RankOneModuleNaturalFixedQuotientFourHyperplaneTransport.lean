module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneCoordinates
public import CFSG.Quasithin.ChapterE.Section06.Obstructions
public import Theory.Representation.SL2BinaryHyperplanes

/-!
# Hyperplane orbit geometry in the original group

The full Hermitian marking is aligned with the actual inner Sylow T∩L.
All subspaces are images of literal subgroups, and every chosen conjugator
lifts to an element of the original L. This retains the original ambient
Sylow in the normalizer and fixed-subgroup conclusions.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry
open OrthogonalFourMinus.FiniteModel OrthogonalFourMinus.HermitianEquiv
open OrthogonalFourMinus.RankOne Matrix.SpecialLinearGroup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L B : Subgroup G} {s : ℕ} [NeZero s]
local instance transportFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance transportBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

private def imageSpace (f : B ≃* Multiplicative (Space s)) (U : Subgroup G) :
    Submodule (ZMod 2) (Space s) :=
  AddSubgroup.toZModSubmodule 2 ((U.subgroupOf B).map f.toMonoidHom).toAddSubgroup

omit [Finite G] in
private theorem mem_imageSpace (f : B ≃* Multiplicative (Space s))
    (U : Subgroup G) (v : B) : (f v).toAdd ∈ imageSpace f U ↔ (v : G) ∈ U := by
  change f v ∈ (U.subgroupOf B).map f.toMonoidHom ↔ v ∈ U.subgroupOf B
  exact mem_map_iff_mem f.injective

omit [Finite G] in
private theorem imageSpace_injective (f : B ≃* Multiplicative (Space s))
    {U W : Subgroup G} (hUB : U ≤ B) (hWB : W ≤ B)
    (he : imageSpace f U = imageSpace f W) : U = W := by
  apply le_antisymm
  · intro v hv
    exact (mem_imageSpace f W ⟨v,hUB hv⟩).mp
      (he ▸ (mem_imageSpace f U ⟨v,hUB hv⟩).mpr hv)
  · intro v hv
    exact (mem_imageSpace f U ⟨v,hWB hv⟩).mp
      (he.symm ▸ (mem_imageSpace f W ⟨v,hWB hv⟩).mpr hv)

private theorem imageSpace_finrank [IsElementaryAbelian 2 B]
    (f : B ≃* Multiplicative (Space s)) (U : Subgroup G) :
    Module.finrank (ZMod 2) (imageSpace f U) + ChapterE.subgroupCorank B U =
      Module.finrank (ZMod 2) (Space s) := by
  have hc := (U.subgroupOf B).card_mul_index
  have hU : Nat.card (U.subgroupOf B) = 2 ^ Module.finrank (ZMod 2) (imageSpace f U) := by
    rw [←card_map_of_injective (K := U.subgroupOf B) (f := f.toMonoidHom) f.injective]
    change Nat.card (imageSpace f U) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hB : Nat.card B = 2 ^ Module.finrank (ZMod 2) (Space s) := by
    rw [Nat.card_congr f.toEquiv]
    change Nat.card (Space s) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hi : (U.subgroupOf B).index = 2 ^ ChapterE.subgroupCorank B U := by
    rw [ChapterE.subgroupCorank_eq_quotient_finrank]
    exact B.relIndex_eq_two_pow_quotient_finrank U
  rw [hU,hi,hB,←pow_add] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc

omit [Finite G] in
private theorem imageSpace_conjugate
    (hLB : L ≤ normalizer (B : Set G))
    (q : L →* Matrix.SpecialLinearGroup (Fin 2) (Field s))
    (f : B ≃* Multiplicative (Space s))
    (hf : ∀ (l : L) (v : B),
      (f (B.normalizerMonoidHom ⟨l,hLB l.property⟩ v)).toAdd =
        SL2.BinarySmall.hermitian s (q l) (f v).toAdd)
    (U : Subgroup G) (hUB : U ≤ B) (l : L) :
    imageSpace f (U.map (MulAut.conj (l : G)).toMonoidHom) =
      (imageSpace f U).map (SL2.BinarySmall.hermitian s (q l)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨v,hv,hvx⟩ := hx
    obtain ⟨u,hu,huv⟩ := hv
    let b : B := ⟨u,hUB hu⟩
    have he : B.normalizerMonoidHom ⟨l,hLB l.property⟩ b = v := Subtype.ext huv
    refine ⟨(f b).toAdd,(mem_imageSpace f U b).mpr hu,?_⟩
    rw [←hf,he]
    exact hvx
  · rintro ⟨x,⟨v,hv,rfl⟩,rfl⟩
    refine ⟨B.normalizerMonoidHom ⟨l,hLB l.property⟩ v,?_,?_⟩
    · exact ⟨v,hv,rfl⟩
    · exact hf l v

private theorem normalizes_of_image_stabilizer
    (hLB : L ≤ normalizer (B : Set G))
    (q : L →* Matrix.SpecialLinearGroup (Fin 2) (Field s))
    (f : B ≃* Multiplicative (Space s))
    (hf : ∀ (l : L) (v : B),
      (f (B.normalizerMonoidHom ⟨l,hLB l.property⟩ v)).toAdd =
        SL2.BinarySmall.hermitian s (q l) (f v).toAdd)
    (U : Subgroup G) (hUB : U ≤ B) (l : L)
    (hl : q l ∈ subspaceStabilizer (SL2.BinarySmall.hermitian s) (imageSpace f U)) :
    (l : G) ∈ normalizer (U : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro x ⟨v,hv,rfl⟩
    let b : B := ⟨v,hUB hv⟩
    apply (mem_imageSpace f U (B.normalizerMonoidHom ⟨l,hLB l.property⟩ b)).mp
    rw [hf]
    exact (hl _).mpr ((mem_imageSpace f U b).mpr hv)
  · rw [card_map_of_injective (MulAut.conj (l : G)).injective]

private theorem invariant_trace_pole_singular
    (p : Space s)
    (hfix : ∀ g ∈ upperUnipotent (Field s),
      g ∈ subspaceStabilizer (SL2.BinarySmall.hermitian s) (traceHyperplane s p)) :
    form s p = 0 := by
  have hp : p ∈ fixedSpace (SL2.BinarySmall.hermitian s) (upperUnipotent (Field s)) := by
    intro g
    apply traceHyperplane_injective s
    change traceHyperplane s (action s g.val p) = traceHyperplane s p
    rw [←traceHyperplane_map]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (hfix g g.property y).mpr hy
    · intro hx
      refine ⟨SL2.BinarySmall.hermitian s g⁻¹ x,?_,
        (SL2.BinarySmall.hermitian s).self_inv_apply g x⟩
      apply (hfix g g.property _).mp
      rwa [(SL2.BinarySmall.hermitian s).self_inv_apply]
  obtain ⟨hb,hz⟩ := (mem_fixedSpace_upper_iff s p).mp hp
  apply Subtype.ext
  change p.val.det = 0
  simp [Matrix.det_fin_two,hb,hz]

private theorem invariant_hyperplane_coordinates [IsElementaryAbelian 2 B]
    (f : B ≃* Multiplicative (Space s))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) :
    ∃ W : Subgroup G, W ≤ B ∧ ChapterE.subgroupCorank B W = 1 ∧
      (T : Subgroup G) ≤ normalizer (W : Set G) := by
  let : Nontrivial (Space s) := (coordinates s).symm.injective.nontrivial
  let ρ := (BinaryConjugationCoordinates.action B f).comp (inclusion hTB)
  obtain ⟨D,hD,hinv⟩ := exists_invariant_binary_hyperplane ρ T.isPGroup'
  let W := ((D.toAddSubgroup.toSubgroup').comap f.toMonoidHom).map B.subtype
  have hWB : W ≤ B := map_subtype_le _
  have hWD : imageSpace f W = D := by
    ext x
    obtain ⟨v,rfl⟩ := f.surjective (Multiplicative.ofAdd x)
    change (f v).toAdd ∈ imageSpace f W ↔ (f v).toAdd ∈ D
    rw [mem_imageSpace]
    exact mem_map_iff_mem B.subtype_injective
  have hc : ChapterE.subgroupCorank B W = 1 := by
    have hh := imageSpace_finrank f W
    rw [hWD] at hh
    omega
  refine ⟨W,hWB,hc,?_⟩
  apply le_normalizer_iff.mpr
  intro t ht w hw
  let v : B := ⟨w,hWB hw⟩
  have hv : (f v).toAdd ∈ D := hWD ▸ (mem_imageSpace f W v).mpr hw
  have hh := hinv ⟨t,ht⟩ (f v).toAdd hv
  change BinaryConjugationCoordinates.action B f ⟨t,hTB ht⟩ (f v).toAdd ∈ D at hh
  rw [BinaryConjugationCoordinates.action_apply] at hh
  rw [←hWD,mem_imageSpace] at hh
  exact hh

omit [Finite G] in
private theorem normalized_image_stabilizer
    (hLB : L ≤ normalizer (B : Set G))
    (q : L →* Matrix.SpecialLinearGroup (Fin 2) (Field s))
    (f : B ≃* Multiplicative (Space s))
    (hf : ∀ (l : L) (v : B),
      (f (B.normalizerMonoidHom ⟨l,hLB l.property⟩ v)).toAdd =
        SL2.BinarySmall.hermitian s (q l) (f v).toAdd)
    (W : Subgroup G) (l : L)
    (hl : (l : G) ∈ normalizer (W : Set G)) :
    q l ∈ subspaceStabilizer (SL2.BinarySmall.hermitian s) (imageSpace f W) := by
  intro x
  obtain ⟨v,rfl⟩ := f.surjective (Multiplicative.ofAdd x)
  change SL2.BinarySmall.hermitian s (q l) (f v).toAdd ∈ imageSpace f W ↔
    (f v).toAdd ∈ imageSpace f W
  rw [←hf,mem_imageSpace,mem_imageSpace]
  exact (mem_normalizer_iff.mp hl v).symm

private theorem fixed_normalizer_le_of_offDiagonal
    (hLB : L ≤ normalizer (B : Set G))
    (q : L →* Matrix.SpecialLinearGroup (Fin 2) (Field s))
    (f : B ≃* Multiplicative (Space s))
    (hf : ∀ (l : L) (v : B),
      (f (B.normalizerMonoidHom ⟨l,hLB l.property⟩ v)).toAdd =
        SL2.BinarySmall.hermitian s (q l) (f v).toAdd)
    (hS : ((T : Subgroup G).subgroupOf L).map q = upperUnipotent (Field s))
    (U : Subgroup G) (hUB : U ≤ B) (z : Field s) (hz : z ≠ 0)
    (hU : imageSpace f U = traceHyperplane s (offDiagonal s z)) :
    B ⊓ centralizer ((T : Subgroup G) ⊓ normalizer (U : Set G) : Set G) ≤ U := by
  rintro x ⟨hxB,hxc⟩
  let v : B := ⟨x,hxB⟩
  apply (mem_imageSpace f U v).mp
  rw [hU]
  apply upper_stabilizer_fixed_le_traceHyperplane s hz
  intro g
  have hg : g.val ∈ ((T : Subgroup G).subgroupOf L).map q := hS.symm ▸ g.property.1
  obtain ⟨l,hl,he⟩ := hg
  have hn : (l : G) ∈ normalizer (U : Set G) :=
    normalizes_of_image_stabilizer hLB q f hf U hUB l (by rw [he,hU]; exact g.property.2)
  have hc : B.normalizerMonoidHom ⟨l,hLB l.property⟩ v = v := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hxc l ⟨hl,hn⟩)
  change SL2.BinarySmall.hermitian s g.val (f v).toAdd = (f v).toAdd
  rw [←he,←hf,hc]

/-- After an actual L-conjugation, every binary hyperplane is either
normalized by the original T, or contains both C_B(T) and C_B(N_T(U)).
No arbitrary-hyperplane fixed-space assertion or external geometry premise
is used. -/
theorem original_hyperplane_conjugate_geometry [IsElementaryAbelian 2 B]
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hm : IsConjugationModel L B (SL2.BinarySmall.hermitian s))
    (U : Subgroup G) (hUB : U ≤ B) (hcor : ChapterE.subgroupCorank B U = 1) :
    ∃ l ∈ L,
      let W := U.map (MulAut.conj l).toMonoidHom
      W ≤ B ∧ ChapterE.subgroupCorank B W = 1 ∧
        ((T : Subgroup G) ≤ normalizer (W : Set G) ∨
          B ⊓ centralizer (T : Set G) ≤ W ∧
          B ⊓ centralizer ((T : Subgroup G) ⊓ normalizer (W : Set G) : Set G) ≤ W) := by
  obtain ⟨q,f,hq,hf,hS⟩ := exists_hermitian_sylow_coordinates hTL hm
  have hd : Module.finrank (ZMod 2) (imageSpace f U) + 1 =
      Module.finrank (ZMod 2) (Space s) := by
    rw [←hcor]
    exact imageSpace_finrank f U
  obtain ⟨p,⟨hp,hpU⟩,_⟩ := existsUnique_traceHyperplane s (imageSpace f U) hd
  have hconj (l : L) : U.map (MulAut.conj (l : G)).toMonoidHom ≤ B :=
    (map_mono hUB).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hm.normalizes l.property))
  have hcorconj (l : L) : ChapterE.subgroupCorank B
      (U.map (MulAut.conj (l : G)).toMonoidHom) = 1 := by
    have he : B.map (MulAut.conj (l : G)).toMonoidHom = B :=
      mem_normalizer_iff_map_conj_eq.mp (hm.normalizes l.property)
    change Nat.log 2 ((U.map (MulAut.conj (l : G)).toMonoidHom).relIndex B) = 1
    conv_lhs => arg 2; arg 2; rw [←he]
    rw [relIndex_map_map_of_injective (f := (MulAut.conj (l : G)).toMonoidHom)
      U B (MulAut.conj (l : G)).injective]
    exact hcor
  by_cases hsing : form s p = 0
  · obtain ⟨W,hWB,hWcor,hTW⟩ := invariant_hyperplane_coordinates (T := T) f hTB
    have hdimW := imageSpace_finrank f W
    rw [hWcor] at hdimW
    obtain ⟨w,⟨hw,hwW⟩,_⟩ := existsUnique_traceHyperplane s (imageSpace f W) hdimW
    have hwsing : form s w = 0 := by
      apply invariant_trace_pole_singular
      intro g hg
      have hg' : g ∈ ((T : Subgroup G).subgroupOf L).map q := hS.symm ▸ hg
      obtain ⟨l,hl,rfl⟩ := hg'
      rw [←hwW]
      exact normalized_image_stabilizer hm.normalizes q f hf W l (hTW hl)
    obtain ⟨a,ha⟩ := singular_pole_normalization s p hp hsing
    obtain ⟨b,hb⟩ := singular_pole_normalization s w hw hwsing
    obtain ⟨l,hl⟩ := hq (b⁻¹*a)
    have he : U.map (MulAut.conj (l : G)).toMonoidHom = W := by
      apply imageSpace_injective f (hconj l) hWB
      rw [imageSpace_conjugate hm.normalizes q f hf U hUB l,hpU,hl,
        traceHyperplane_map,map_mul,Module.End.mul_apply,ha,←hb,
        (action s).inv_self_apply,←hwW]
    refine ⟨l,l.property,hconj l,hcorconj l,Or.inl ?_⟩
    rwa [he]
  · obtain ⟨g,z,hz,hg,_⟩ := nonsingular_pole_normalization s p hsing
    obtain ⟨l,hl⟩ := hq g
    have hU' : imageSpace f (U.map (MulAut.conj (l : G)).toMonoidHom) =
        traceHyperplane s (offDiagonal s z) := by
      rw [imageSpace_conjugate hm.normalizes q f hf U hUB l,hpU,hl,traceHyperplane_map,hg]
    have hfN := fixed_normalizer_le_of_offDiagonal hm.normalizes q f hf hS
      (U.map (MulAut.conj (l : G)).toMonoidHom) (hconj l) z hz hU'
    exact ⟨l,l.property,hconj l,hcorconj l,Or.inr
      ⟨(inf_le_inf_left B (centralizer_le inf_le_left)).trans hfN,hfN⟩⟩

end CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry

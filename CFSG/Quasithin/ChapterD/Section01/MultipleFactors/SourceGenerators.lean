module
public import CFSG.Quasithin.ChapterD.Section01.SourceElementary
public import Theory.Representation.BinaryOffender.InternalGenerators

/-!
# Literal conjugate generators and the original qrc ratio

Every G₂-conjugate of V is normalized by O₂(G₂), and lies in the actual
span U. These conjugates define invariant subrepresentations for any actor
B≤O₂(G₂). Conjugation back into G₁ gives an equivariant injection of each
faithful generator image into G₁/C_G₁(V), so its quadratic ratio is at least
the original ratio. Their finite sequence generates the entire original U.

Source: Aschbacher–Smith D.1.3(a–b), printed pp.173–174.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}
  (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)

abbrev conjugateSeed (g : G₂) : Subgroup G₂ :=
  (V.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf G₂

include d hV in
theorem conjugateSeed_le_right (g : G₂) :
    V.map (MulAut.conj (g : G)).toMonoidHom ≤ G₂ :=
  (le_iSup (fun x : G₂ => V.map (MulAut.conj (x : G)).toMonoidHom) g).trans
    ((span_le_right_core d hV).trans (twoCore_le G₂))

theorem conjugateSeed_le_span (g : G₂) :
    conjugateSeed (V := V) g ≤ (conjugateSpan G₂ V).subgroupOf G₂ := by
  intro x hx
  exact (le_iSup (fun x : G₂ => V.map (MulAut.conj (x : G)).toMonoidHom) g) hx

include d in
theorem conjugateSeed_core_normalized (g : G₂) :
    pCore 2 G₂ ≤ normalizer (conjugateSeed (V := V) g : Set G₂) := by
  have hn : twoCoreIn G₂ ≤ normalizer (V : Set G) :=
    ((right_core_le_sylow d).trans (sylow_le_left d)).trans d.module_normalized
  have he : (twoCoreIn G₂).map (MulAut.conj (g : G)).toMonoidHom = twoCoreIn G₂ :=
    mem_normalizer_iff_map_conj_eq.mp (twoCore_normalized G₂ g.property)
  have hn' : twoCoreIn G₂ ≤ normalizer (V.map (MulAut.conj (g : G)).toMonoidHom : Set G) := by
    rw [← he]
    exact (map_mono hn).trans (le_normalizer_map _)
  apply le_trans _ (le_normalizer_comap G₂.subtype)
  intro x hx
  exact hn' (mem_map_of_mem G₂.subtype hx)

include d hV in
theorem iSup_conjugateSeed : (⨆ g : G₂, conjugateSeed (V := V) g) =
    (conjugateSpan G₂ V).subgroupOf G₂ := by
  apply Subgroup.map_injective G₂.subtype_injective
  rw [Subgroup.map_iSup, map_subgroupOf_eq_of_le ((span_le_right_core d hV).trans (twoCore_le G₂))]
  change (⨆ g : G₂, (conjugateSeed (V := V) g).map G₂.subtype) = _
  simp_rw [conjugateSeed, map_subgroupOf_eq_of_le (conjugateSeed_le_right d hV _)]
  rfl

variable [IsElementaryAbelian 2 V]
  [IsElementaryAbelian 2 ((conjugateSpan G₂ V).subgroupOf G₂)]

noncomputable def conjugateGenerator (B : Subgroup G₂) (hB : B ≤ pCore 2 G₂) (g : G₂) :
    Subrepresentation ((normalRepresentation ((conjugateSpan G₂ V).subgroupOf G₂)).comp B.subtype) :=
  internalGenerator _ B (conjugateSeed (V := V) g) (hB.trans (conjugateSeed_core_normalized d g))

include hV in
theorem conjugateGenerator_ratio (B : Subgroup G₂) (hB : B ≤ pCore 2 G₂) (g : G₂) :
    quadraticRatio (imageRepresentation G₁ V d.module_normalized) ≤
      quadraticRatio (Representation.BinaryOffender.imageRepresentation
        (conjugateGenerator d B hB g).toRepresentation) := by
  let U := (conjugateSpan G₂ V).subgroupOf G₂
  let Wg := V.map (MulAut.conj (g : G)).toMonoidHom
  let W := conjugateSeed (V := V) g
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf (conjugateSeed_le_right d hV g)
  let e := (subgroupOfEquivOfLe (conjugateSeed_le_right d hV g)).trans
    ((MulAut.conj (g : G)).subgroupMap V).symm
  let E₀ : Additive W ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  let E : (conjugateGenerator d B hB g).toSubmodule ≃ₗ[ZMod 2] Additive V :=
    (internalGeneratorEquiv U B W (hB.trans (conjugateSeed_core_normalized d g))
    (conjugateSeed_le_span g)).symm.trans E₀
  let f₀ : B →* G := (MulAut.conj (g : G)⁻¹).toMonoidHom.comp (G₂.subtype.comp B.subtype)
  have hf₀ : ∀ b, f₀ b ∈ G₁ := by
    intro b
    apply (right_core_le_sylow d).trans (sylow_le_left d)
    exact le_normalizer_iff.mp (twoCore_normalized G₂) (g : G)⁻¹ (G₂.inv_mem g.property)
      (b.val : G) (mem_map_of_mem G₂.subtype (hB b.property))
  let f := (actionHom G₁ V d.module_normalized).rangeRestrict.comp (f₀.codRestrict G₁ hf₀)
  have hEval (v : (conjugateGenerator d B hB g).toSubmodule) :
      ((E v).toMul : G) = (g : G)⁻¹ * (v.val.toMul.val : G) * (g : G) := by
    obtain ⟨w,rfl⟩ := (internalGeneratorEquiv U B W
      (hB.trans (conjugateSeed_core_normalized d g)) (conjugateSeed_le_span g)).surjective v
    change ((E₀ ((internalGeneratorEquiv U B W
      (hB.trans (conjugateSeed_core_normalized d g)) (conjugateSeed_le_span g)).symm
        ((internalGeneratorEquiv U B W
          (hB.trans (conjugateSeed_core_normalized d g)) (conjugateSeed_le_span g)) w))).toMul : G) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  apply quadraticRatio_le_image_of_equivariant _ _ f
    (imageRepresentation_injective G₁ V d.module_normalized) E
  intro b v
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [hEval]
  change (g : G)⁻¹ * ((b.val : G) * (v.val.toMul.val : G) * (b.val : G)⁻¹) * (g : G) =
    f₀ b * ((E v).toMul : G) * (f₀ b)⁻¹
  rw [hEval]
  change (g : G)⁻¹ * ((b.val : G) * (v.val.toMul.val : G) * (b.val : G)⁻¹) * (g : G) =
    ((g : G)⁻¹ * (b.val : G) * ((g : G)⁻¹)⁻¹) *
      ((g : G)⁻¹ * (v.val.toMul.val : G) * (g : G)) *
        ((g : G)⁻¹ * (b.val : G) * ((g : G)⁻¹)⁻¹)⁻¹
  group

include hV in
theorem exists_conjugateGenerator_sequence (B : Subgroup G₂) (hB : B ≤ pCore 2 G₂) :
    ∃ (n : ℕ) (W : ℕ → Subrepresentation
        ((normalRepresentation ((conjugateSpan G₂ V).subgroupOf G₂)).comp B.subtype)),
      generatingSpan _ W n = ⊤ ∧
        ∀ i < n, quadraticRatio (imageRepresentation G₁ V d.module_normalized) ≤
          quadraticRatio (Representation.BinaryOffender.imageRepresentation (W i).toRepresentation) := by
  let := d.finite_right
  let U := (conjugateSpan G₂ V).subgroupOf G₂
  have hg : (⨆ g : G₂, conjugateGenerator d B hB g) = ⊤ :=
    iSup_internalGenerator_eq_top U B (fun g => conjugateSeed (V := V) g)
      (fun g => hB.trans (conjugateSeed_core_normalized d g))
      (fun g => conjugateSeed_le_span g) (iSup_conjugateSeed d hV)
  obtain ⟨n,a,ha⟩ := exists_generatingSequence _ (conjugateGenerator d B hB) hg
  exact ⟨n,fun i => conjugateGenerator d B hB (a i),ha,
    fun i _ => conjugateGenerator_ratio d hV B hB (a i)⟩

end CFSG.Quasithin.ChapterD.UniqueFactor

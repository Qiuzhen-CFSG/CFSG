module
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceGenerators
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.Actors
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic

/-!
# Minimum actor rank on the original M22-code conjugate span

Each literal H-conjugate of the original qrc module carries the same native
M22-code action, via conjugation back to the original normalizer image. The
map retains its full kernel. Since a nonidentity elementary code actor moves
at least three dimensions, an elementary subgroup of O₂(H) moving at most
two dimensions on the H-span centralizes every conjugate and hence the span.
The sharp qrc rank and centralizer equalities therefore force the selected
actor to have rank at least two modulo O₂(H).

This proves the minimum-rank step used in original 3.1.9(4,6) and 8.2.2(1)
for the code branch. It does not classify the full parabolic quotient.
Source: Aschbacher--Smith, printed pp.577,715; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open ChapterD ChapterD.UniqueFactor MathieuCode
variable {G : Type*} [Group G] [Finite G] {G₁ H T V : Subgroup G}
  (d : QRCConfiguration G₁ H T V) (hV : V ≤ twoCoreIn H)
  [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]

omit [Finite G] in
include hV in
/-- Conjugation back gives actual code coordinates on each original generator. -/
theorem conjugate_code_marking
    (a : internalActionImage G₁ V d.module_normalized →* m22PairStabilizer)
    (E : Additive V ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ x v, E (ChapterD.UniqueFactor.imageRepresentation G₁ V d.module_normalized x v) =
      m22OuterCodeRepresentation (a x) (E v))
    (B : Subgroup H) (hB : B ≤ pCore 2 H) (g : H) :
    ∃ f : B →* m22PairStabilizer,
      ∃ F : (conjugateGenerator d B hB g).toSubmodule ≃ₗ[ZMod 2] M22Code,
        ∀ b v, F ((conjugateGenerator d B hB g).toRepresentation b v) =
          m22OuterCodeRepresentation (f b) (F v) := by
  let U := (conjugateSpan H V).subgroupOf H
  let Wg := V.map (MulAut.conj (g : G)).toMonoidHom
  let W := conjugateSeed (V := V) g
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf (conjugateSeed_le_right d hV g)
  let e := (subgroupOfEquivOfLe (conjugateSeed_le_right d hV g)).trans
    ((MulAut.conj (g : G)).subgroupMap V).symm
  let E₀ : Additive W ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  let E₁ : (conjugateGenerator d B hB g).toSubmodule ≃ₗ[ZMod 2] Additive V :=
    (internalGeneratorEquiv U B W (hB.trans (conjugateSeed_core_normalized d g))
    (conjugateSeed_le_span g)).symm.trans E₀
  let f₀ : B →* G := (MulAut.conj (g : G)⁻¹).toMonoidHom.comp (H.subtype.comp B.subtype)
  have hf₀ : ∀ b, f₀ b ∈ G₁ := by
    intro b
    apply (right_core_le_sylow d).trans (sylow_le_left d)
    exact le_normalizer_iff.mp (twoCore_normalized H) (g : G)⁻¹ (H.inv_mem g.property)
      (b.val : G) (mem_map_of_mem H.subtype (hB b.property))
  let f := (ChapterD.UniqueFactor.actionHom G₁ V d.module_normalized).rangeRestrict.comp
    (f₀.codRestrict G₁ hf₀)
  have hEval (v : (conjugateGenerator d B hB g).toSubmodule) :
      ((E₁ v).toMul : G) = (g : G)⁻¹ * (v.val.toMul.val : G) * (g : G) := by
    obtain ⟨w,rfl⟩ := (internalGeneratorEquiv U B W
      (hB.trans (conjugateSeed_core_normalized d g)) (conjugateSeed_le_span g)).surjective v
    change ((E₀ ((internalGeneratorEquiv U B W
      (hB.trans (conjugateSeed_core_normalized d g)) (conjugateSeed_le_span g)).symm
        ((internalGeneratorEquiv U B W
          (hB.trans (conjugateSeed_core_normalized d g)) (conjugateSeed_le_span g)) w))).toMul : G) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have he (b : B) (v : (conjugateGenerator d B hB g).toSubmodule) :
      E₁ ((conjugateGenerator d B hB g).toRepresentation b v) =
        ChapterD.UniqueFactor.imageRepresentation G₁ V d.module_normalized (f b) (E₁ v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hEval]
    change (g : G)⁻¹ * ((b.val : G) * (v.val.toMul.val : G) * (b.val : G)⁻¹) * (g : G) =
      f₀ b * ((E₁ v).toMul : G) * (f₀ b)⁻¹
    rw [hEval]
    change (g : G)⁻¹ * ((b.val : G) * (v.val.toMul.val : G) * (b.val : G)⁻¹) * (g : G) =
      ((g : G)⁻¹ * (b.val : G) * ((g : G)⁻¹)⁻¹) *
        ((g : G)⁻¹ * (v.val.toMul.val : G) * (g : G)) *
          ((g : G)⁻¹ * (b.val : G) * ((g : G)⁻¹)⁻¹)⁻¹
    group
  exact ⟨a.comp f,E₁.trans E,fun b v => (congrArg E (he b v)).trans (hE (f b) (E₁ v))⟩

include hV in
/-- Small displacement on the span forces centralization of every code conjugate. -/
theorem core_code_small_displacement_centralizes
    (a : internalActionImage G₁ V d.module_normalized →* m22PairStabilizer)
    (E : Additive V ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ x v, E (ChapterD.UniqueFactor.imageRepresentation G₁ V d.module_normalized x v) =
      m22OuterCodeRepresentation (a x) (E v))
    (B : Subgroup H) [IsElementaryAbelian 2 B] (hB : B ≤ pCore 2 H)
    (hsmall : fixedCodim (normalRepresentation ((conjugateSpan H V).subgroupOf H)) B ≤ 2) :
    B ≤ centralizer ((conjugateSpan H V).subgroupOf H : Set H) := by
  let U := (conjugateSpan H V).subgroupOf H
  let τ := (normalRepresentation U).comp B.subtype
  have hsmall' : fixedCodim τ ⊤ ≤ 2 := by
    rw [fixedCodim, fixedSpace_comp_map, ← MonoidHom.range_eq_map, range_subtype]
    exact hsmall
  have hfixed (g : H) (b : B)
      (v : (conjugateGenerator d B hB g).toSubmodule) :
      (conjugateGenerator d B hB g).toRepresentation b v = v := by
    obtain ⟨f,F,hF⟩ := conjugate_code_marking d hV a E hE B hB g
    have hf : f b = 1 := by
      by_contra hne
      have hp : (f b)^2 = 1 := by
        rw [← map_pow]
        simpa only [map_one] using congrArg f (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 B) b)
      have ho : orderOf (f b) = 2 := orderOf_eq_prime hp hne
      have hl := (m22Outer_involution_displacement_ge_three (f b) ho).1
      have he := fixedCodim_map_equivariant
        (conjugateGenerator d B hB g).toRepresentation m22OuterCodeRepresentation f F hF (zpowers b)
      rw [MonoidHom.map_zpowers] at he
      have hu := (NaturalTensor.fixedCodim_mono
        (conjugateGenerator d B hB g).toRepresentation (show zpowers b ≤ ⊤ from le_top)).trans
          (fixedCodim_subrepresentation_le τ (conjugateGenerator d B hB g) ⊤)
      omega
    apply F.injective
    rw [hF,hf,map_one,Module.End.one_apply]
  have hc : U ≤ centralizer (B : Set H) := by
    dsimp only [U]
    rw [← iSup_conjugateSeed d hV]
    apply iSup_le
    intro g w hw b hb
    let v : (conjugateGenerator d B hB g).toSubmodule :=
      ⟨Additive.ofMul ⟨w,conjugateSeed_le_span g hw⟩,hw⟩
    have hh := congrArg (fun v : (conjugateGenerator d B hB g).toSubmodule =>
      (v.val.toMul : H)) (hfixed g ⟨b,hb⟩ v)
    change b * w * b⁻¹ = w at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  exact le_centralizer_iff.mp hc

include hV in
/-- The sharp original actor cannot have rank one modulo the two-core. -/
theorem code_sharp_actor_rank_lower
    (a : internalActionImage G₁ V d.module_normalized →* m22PairStabilizer)
    (E : Additive V ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ x v, E (ChapterD.UniqueFactor.imageRepresentation G₁ V d.module_normalized x v) =
      m22OuterCodeRepresentation (a x) (E v))
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hnc : ¬ A ≤ centralizer ((conjugateSpan H V).subgroupOf H : Set H))
    (hcod : 2 * Nat.log 2 ((pCore 2 H).relIndex A) =
      fixedCodim (normalRepresentation ((conjugateSpan H V).subgroupOf H)) A)
    (hcent : (conjugateSpan H V).subgroupOf H ⊓ centralizer (A : Set H) =
      (conjugateSpan H V).subgroupOf H ⊓ centralizer (A ⊓ pCore 2 H : Set H)) :
    2 ≤ Nat.log 2 ((pCore 2 H).relIndex A) := by
  by_contra! hs
  let B := A ⊓ pCore 2 H
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (inf_le_left : B ≤ A)
  have hb : fixedCodim (normalRepresentation ((conjugateSpan H V).subgroupOf H)) B ≤ 2 :=
    (NaturalTensor.fixedCodim_mono _ (show B ≤ A from inf_le_left)).trans (by omega)
  have hc := core_code_small_displacement_centralizes d hV a E hE B inf_le_right hb
  have he : (conjugateSpan H V).subgroupOf H ⊓ centralizer (B : Set H) =
      (conjugateSpan H V).subgroupOf H := inf_eq_left.mpr (le_centralizer_iff.mp hc)
  have he' := hcent.trans he
  exact hnc (le_centralizer_iff.mp (inf_eq_left.mp he'))

end CFSG.Quasithin.Chapter8.MathieuShadowRows

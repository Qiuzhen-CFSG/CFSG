module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearOvergroupSaturation
public import Theory.Representation.PSL3Two.SixSpaceNormalizers
public import Theory.Representation.BinaryOffender.NormalizerSupplement

/-!
# The actual overgroup supplement after omega-module equality

The original component is normal in each local overgroup. Once its omega
module equals the original six-space, the marked normalizer calculations
for natural plus dual and both Fano cores place the larger two-residual
inside the component times the full action kernel. The common Sylow then
gives the literal overgroup product. The equal-kernel branch now supplies
both module equality and this product, with every original map retained.

The unequal-kernel replacement case and the source residual commutator
premise remain separate obligations; this does not assert all of 13.4.7.
Structural1222 and Source1332OneTwo retain their genuine earlier scope.
Source: Aschbacher–Smith 13.4.7(2), printed p.902.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource NoncentralChiefRefinement
open Representation.BinaryOffender BinaryLinearThree.FanoDecomposition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK hres h structural hout hindexL eK

/-- The source's overgroup supplement follows from equality of the literal
omega modules, for all three original six-space models. -/
theorem original_pair_linear_overgroup_supplement_of_omega_eq
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G))
    (heq : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y =
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)) :
    (Y : Set G) = ((A ⊔ B : Subgroup G) : Set G) *
      (Y ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G))
        (A ⊔ B) : Set G) : Subgroup G) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  have hTY : (T : Subgroup G) ≤ Y := (hTA.trans le_sup_left).trans hY.2
  have hCY : C ≤ Y := (map_subtype_le K).trans hY.2
  have hWY : W ≤ Y := (conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
      X.le_normalizer).trans hY.2
  have hYW : Y ≤ normalizer (W : Set G) := by
    change Y ≤ normalizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G)
    rw [←heq]
    exact le_normalizer_conjugateSpanBy Z Y
  let U := W.subgroupOf Y
  let J := C.subgroupOf Y
  let : U.Normal := (normal_subgroupOf_iff_le_normalizer hWY).mpr hYW
  let : J.Normal := (normal_subgroupOf_iff_le_normalizer hCY).mpr
    (original_pair_component_overgroup_normal h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK Y hY)
  obtain ⟨heW,e,hA,hB,hS,hm,_⟩ := original_pair_linear_whole_module h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := heW
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hWY).toMonoidHom (subgroupOfEquivOfLe hWY).injective
  let ρ := normalRepresentation U
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  let j : J ≃* C := subgroupOfEquivOfLe hCY
  let fJ := f.comp j.toMonoidHom
  have hfJ : Function.Surjective fJ := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp j.surjective)
  let a : Additive W ≃ₗ[ZMod 2] Additive U :=
    LinearEquiv.ofBijective
      ((subgroupOfEquivOfLe hWY).symm.toMonoidHom.toAdditive.toZModLinearMap 2)
      (subgroupOfEquivOfLe hWY).symm.bijective
  have step {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
      (σ : Representation (ZMod 2) BinaryLinearThree.Group M)
      (em : Representation.Equiv (σ.comp f)
        (Representation.elementaryRepresentation (p := 2)
          (W.normalizerMonoidHom.comp (inclusion
            ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))))))
      (hr : (pResidual 2 (linearNormalizer σ)).map (linearNormalizer σ).subtype ≤
        actionImage σ) : (J ⊔ ρ.asGroupHom.ker) ⊔ (T.subtype hTY : Subgroup Y) = ⊤ := by
    apply sylow_supplement_of_model_normalizer ρ J (T.subtype hTY) fJ hfJ σ
      (em.toLinearEquiv.trans a) _ hr
    intro k v
    have hv := LinearMap.congr_fun (em.isIntertwining' (j k)) v
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : Additive W => w.toMul.val) hv
  have hsupp : (J ⊔ ρ.asGroupHom.ker) ⊔ (T.subtype hTY : Subgroup Y) = ⊤ := by
    rcases hm with hm | hm | hm
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.SixSpaceNormalizers.natural_dual_residual
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.SixSpaceNormalizers.point_residual
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.SixSpaceNormalizers.line_residual
  have hk : ρ.asGroupHom.ker = centralizer (U : Set Y) := by
    ext y
    change ρ.asGroupHom y = 1 ↔ y ∈ centralizer (U : Set Y)
    constructor
    · intro hy w hw
      have hv := congrArg (fun z : (Module.End (ZMod 2) (Additive U))ˣ =>
        z.val (Additive.ofMul (⟨w,hw⟩ : U))) hy
      have hc : y * w * y⁻¹ = w := congrArg (fun v : Additive U => v.toMul.val) hv
      exact (mul_inv_eq_iff_eq_mul.mp hc).symm
    · intro hy
      apply Units.ext
      apply LinearMap.ext
      intro w
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hy w.toMul.val w.toMul.property).symm
  have hcent : (centralizer (U : Set Y)).map Y.subtype =
      Y ⊓ centralizer (W : Set G) := by
    have hh := map_inf_centralizer_of_injective Y.subtype Y.subtype_injective
      (⊤ : Subgroup Y) U
    simpa only [top_inf_eq,←MonoidHom.range_eq_map,range_subtype,
      U,map_subgroupOf_eq_of_le hWY] using hh.symm
  have hsup := congrArg (Subgroup.map Y.subtype) hsupp
  rw [hk,Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hCY,hcent,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTY,
    ←MonoidHom.range_eq_map,range_subtype] at hsup
  have hgen := (original_pair_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2
  have he : X ⊔ (Y ⊓ centralizer (W : Set G)) = Y := by
    change (A ⊔ B) ⊔ (Y ⊓ centralizer (W : Set G)) = Y
    rw [hgen]
    exact (sup_right_comm C (T : Subgroup G) (Y ⊓ centralizer (W : Set G))).trans hsup
  calc
    (Y : Set G) = (X ⊔ (Y ⊓ centralizer (W : Set G)) : Subgroup G) :=
      congrArg (fun P : Subgroup G => (P : Set G)) he.symm
    _ = (X : Set G) * (Y ⊓ centralizer (W : Set G) : Subgroup G) :=
      coe_mul_of_left_le_normalizer_right _ _
        (hY.2.trans ((le_inf Y.le_normalizer
          (hYW.trans (normalizer_le_normalizer_centralizer W))).trans
            inf_normalizer_le_normalizer_inf))
/-- The equal-kernel branch now gives both conclusions of 13.4.7(2),
including the literal product by the full overgroup action centralizer. -/
theorem original_pair_linear_overgroup_formula_of_same_actor_kernel
    (E : Subgroup G) (hE : E ∈ ChapterB.thompsonFamily (T : Subgroup G) 1)
    (hneE : ¬ E ≤ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G))
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G))
    (hker : E ⊓ centralizer
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G) =
      E ⊓ centralizer
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y : Set G)) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y =
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) ∧
    (Y : Set G) = ((A ⊔ B : Subgroup G) : Set G) *
      (Y ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G))
        (A ⊔ B) : Set G) : Subgroup G) := by
  have he := original_pair_linear_overgroup_eq_of_same_actor_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres h structural hout hindexL eK
    E hE hneE Y hY hker
  exact ⟨he,original_pair_linear_overgroup_supplement_of_omega_eq h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres h structural hout hindexL eK Y hY he⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

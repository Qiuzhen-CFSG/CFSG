module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearWholeModule
public import Theory.Representation.PSL3Two.FanoNonFF
public import Theory.Representation.NormalElementaryQuotient.ComponentModel

/-!
# Thompson normality in the original linear amalgam

The full two-core quotient is filled by the selected component. Its actual
omega orbit is natural plus dual or one of the two Fano cores; each has
both opposite natural constituents and admits no FF offender. Applying the
normal elementary action criterion to the original quotient makes J(T)
normal in the original join. All component, kernel and ambient maps remain
literal. Structural1222 and Source1332OneTwo retain their earlier producers.
Source: Aschbacher–Smith 13.4.7(1ii), printed pp.900–901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open BinaryLinearThree.FanoDecomposition Representation.BinaryOffender
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The original join normalizes the elementary Thompson subgroup of its common Sylow. -/
theorem original_pair_linear_thompson_normal
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    A ⊔ B ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  let E := U.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  let S := T.subtype hTX
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : E.Normal := hred.normal
  let : IsElementaryAbelian 2 E := hred.elementary
  obtain ⟨heU,e,hA,hB,hS,hm,_⟩ := original_pair_linear_whole_module h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := heU
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  let j : K ≃* C := K.equivMapOfInjective X.subtype X.subtype_injective
  let fK := f.comp j.toMonoidHom
  have hfK : Function.Surjective fK := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp j.surjective)
  have hns : ¬ Group.IsSolvable X := by
    intro hh
    let := hh
    exact hK.not_isSolvable inferInstance
  have hfull := original_pair_full_action_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB hres hns
  have hcent : centralizer (E : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    have hh := map_inf_centralizer_of_injective X.subtype X.subtype_injective
      (⊤ : Subgroup X) E
    have heq : (centralizer (E : Set X)).map X.subtype = X ⊓ centralizer (U : Set G) := by
      simpa only [top_inf_eq,←MonoidHom.range_eq_map,range_subtype,
        E,map_subgroupOf_eq_of_le hUX] using hh.symm
    exact heq.trans hfull
  have hgen : K ⊔ centralizer (E : Set X) = ⊤ := by
    rw [hcent]
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype]
    exact (original_pair_linear_core_supplement h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK eK).2
  have hk : fK.ker = (centralizer (E : Set X)).subgroupOf K := by
    have hqker := (original_pair_component_twoCore_image h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).1
    have hp : (pCore 2 X).subgroupOf K = pCore 2 K := by
      have hh : ((QuotientGroup.mk' (pCore 2 X)).subgroupMap K).ker =
          (pCore 2 X).subgroupOf K := by
        ext k
        change ((QuotientGroup.mk' (pCore 2 X)).subgroupMap K) k = 1 ↔ k.val ∈ pCore 2 X
        rw [Subtype.ext_iff]
        exact QuotientGroup.eq_one_iff k.val
      exact hh.symm.trans hqker
    rw [hcent,hp]
    change (f.comp j.toMonoidHom).ker = _
    rw [←MonoidHom.comap_ker,MonoidHom.ker_comp_of_injective _ _ e.injective,
      QuotientGroup.ker_mk',←pCore_map_iso 2 j,comap_map_eq_self_of_injective j.injective]
  have step {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
      (σ : Representation (ZMod 2) BinaryLinearThree.Group M)
      (eU : Representation.Equiv (σ.comp f)
        (Representation.elementaryRepresentation (p := 2)
          (U.normalizerMonoidHom.comp (inclusion
            ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))))))
      (hn : ¬ IsFFModule σ) : (elementaryAbelianMaxJ (S : Subgroup X)).Normal := by
    let a : Additive U ≃ₗ[ZMod 2] Additive E :=
      LinearEquiv.ofBijective
        ((subgroupOfEquivOfLe hUX).symm.toMonoidHom.toAdditive.toZModLinearMap 2)
        (subgroupOfEquivOfLe hUX).symm.bijective
    apply Representation.NormalElementaryQuotient.thompson_normal_of_component_model
      S E K hgen (by rw [hcent]; exact pCore_isPGroup) fK hfK hk σ
      (eU.toLinearEquiv.trans a) _ hn
    intro k v
    have he := LinearMap.congr_fun (eU.isIntertwining' (j k)) v
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : Additive U => w.toMul.val) he
  have hnormal : (elementaryAbelianMaxJ (S : Subgroup X)).Normal := by
    rcases hm with hm | hm | hm
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.FanoNonFF.sum_not_ff
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.FanoNonFF.point_not_ff
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.FanoNonFF.line_not_ff
  let := hnormal
  have hnorm := (elementaryAbelianMaxJ (S : Subgroup X)).le_normalizer_map X.subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
    ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] at hnorm
  exact hnorm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

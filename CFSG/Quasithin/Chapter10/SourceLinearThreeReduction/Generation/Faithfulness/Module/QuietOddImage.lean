module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.QuietImage
public import Theory.Representation.BinaryOffender.SylowFixedCentralizer
public import Theory.Representation.ElementaryPerfectSplit

/-!
# Odd normalized overgroups of the quiet kernel image

The actual Hall image need not itself be Sylow invariant. Containment in
any odd subgroup normalized by the Sylow image suffices: the pointwise
kernel of that odd group on the Sylow-fixed space is trivial. The action
used here is the faithful automorphism action on the unchanged V_M.

This supplies a weaker alternative to normalizing an individual elementary
kernel image, particularly when the Sylow permutes several odd factors.
Source: the coprime fixed-point argument in Aschbacher--Smith 4.4.14 and
10.2.3(2), printed pp.624--625,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- An odd normalized overgroup detects every quiet odd actor on the
literal full module; normality of that actor is unnecessary. -/
theorem source_omegaCentralizingActor_fixes_of_image_le_odd_normalized
    (A : Subgroup G) (hAM : A ≤ D.maximalLocal)
    (hz : A ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (P : Subgroup (MulAut D.fullModule)) (ho : Odd (Nat.card P))
    (hSP : ((T : Subgroup G).subgroupOf D.maximalLocal).map
      (sourceFullModuleConjugation D) ≤ normalizer (P : Set (MulAut D.fullModule)))
    (hAP : (A.subgroupOf D.maximalLocal).map (sourceFullModuleConjugation D) ≤ P) :
    A ≤ centralizer (D.fullModule : Set G) := by
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let q := sourceFullModuleConjugation D
  let ρ := elementaryRepresentation (p := 2) (MonoidHom.id (MulAut D.fullModule))
  let S := ((T : Subgroup G).subgroupOf D.maximalLocal).map q
  have hf : Function.Injective ρ := by
    intro a b hab
    apply MulEquiv.ext
    intro v
    have he := LinearMap.congr_fun hab (Additive.ofMul v)
    exact congrArg Additive.toMul he
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype.map q
  have hk := odd_kernel_on_two_fixed_eq_bot ρ hf P S ho hSP hS
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hVT := D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)
  have hzero : A.subgroupOf D.maximalLocal ≤ q.ker := by
    intro a ha
    have hmem : q a ∈ subspaceKernel ρ (fixedSpace ρ S) P := by
      refine ⟨hAP (mem_map_of_mem q ha),?_⟩
      intro v hv
      have hvT : (v.toMul : G) ∈ centralizer (T : Set G) := by
        intro t ht
        let tM : D.maximalLocal := ⟨t,hTM ht⟩
        have htS : q tM ∈ S := mem_map_of_mem q ht
        have he := congrArg (fun w : Additive D.fullModule => (w.toMul : G)) (hv ⟨q tM,htS⟩)
        change (q tM v.toMul : G) = (v.toMul : G) at he
        rw [sourceFullModuleConjugation_apply] at he
        exact mul_inv_eq_iff_eq_mul.mp he
      have hvZ : (v.toMul : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) :=
        (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
          ⟨hVT v.toMul.property,elemPow_eq_one_of_isElementaryAbelian _ v.toMul.property,
            fun t ht => hvT t ht⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      change (q a v.toMul : G) = (v.toMul : G)
      rw [sourceFullModuleConjugation_apply]
      have hc : (v.toMul : G) * (a : G) = (a : G) * (v.toMul : G) := hz ha _ hvZ
      rw [←hc,mul_inv_cancel_right]
    exact mem_bot.mp (hk ▸ hmem)
  intro a ha
  exact (show (⟨a,hAM ha⟩ : D.maximalLocal) ∈
    (centralizer (D.fullModule : Set G)).subgroupOf D.maximalLocal from
    sourceFullModuleConjugation_ker D ▸ hzero ha)

/-- The quiet original Hall kernel fixes V_M whenever its full image lies
in an odd subgroup normalized by the actual Sylow image. -/
theorem source_quiet_hall_kernel_fixes_of_image_le_odd_normalized
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H)
    (P : Subgroup (MulAut D.fullModule)) (ho : Odd (Nat.card P))
    (hSP : ((T : Subgroup G).subgroupOf D.maximalLocal).map
      (sourceFullModuleConjugation D) ≤ normalizer (P : Set (MulAut D.fullModule)))
    (hBP : ((B.map H.subtype ⊓ sectionCentralizer (localOrbit T L)).subgroupOf
      D.maximalLocal).map (sourceFullModuleConjugation D) ≤ P) :
    B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G) :=
  source_omegaCentralizingActor_fixes_of_image_le_odd_normalized D _
    (inf_le_right.trans ((le_sectionCentralizer_iff _ _).mp le_rfl).1)
    ((inf_le_left.trans (map_subtype_le B)).trans
      (source_hstar_centralizes_omega_of_local_thompson_centralizes D hJ hH)) P ho hSP hBP

end CFSG.Quasithin.Chapter10

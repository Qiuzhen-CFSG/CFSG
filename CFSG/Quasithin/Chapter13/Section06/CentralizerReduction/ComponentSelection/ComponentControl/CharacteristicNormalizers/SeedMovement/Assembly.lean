module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.ThompsonReplacement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.ActionTransfer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.AdequateFactorization
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration
/-!
# Seed movement from the earlier characteristic-two centralizer

For H = K₀C_T(v), form W = ⟨z^H⟩ inside H. The earlier 13.6.6
makes W elementary abelian, and the Sylow-central seed makes H/C_H(W)
two-reduced. If the image of K₀ is nonquasisimple, the corrected universal
B.5.6 contract and B.2.5–7 put a moving local component in the Thompson
normalizer. Its normalization of the nontrivial characteristic J(C_T(v))
contradicts the permitted universal assertion 13.6.16(1). Thus the component
image is quasisimple. Radical supplements cover that image and therefore
move z; in particular the parent's actual normalizer residual moves z.

This independent route invokes no conclusion of 13.6.8–15 and does not
assume that the radical fixes z. The only classification input is the native
adequate B.5.6 contract, whose outer clause keeps the actual A₆–C₃ group
configuration without the disputed whole-module splitting.

The final adapter uses the actual marked vectors, Sylow image and literal
residual formula. These are conditional source-bound transfers: 13.6.6 and
the marked local configuration remain to be supplied by the existing task
`qt-13-06-characteristic-two`. The seed-movement task retains their discharge
before claiming a source-only result. The parent characteristic-normalizer
task retains strict-inequality assembly and the earlier universal inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.2–6, printed pp.926–928; 13.6.16(2), p.930; B.2.5–7 and B.2.14,
pp.76–78; B.5.6, p.105. The change of route is the local seed-action
case split described above, replacing the unexplained movement transfer.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement
open NonquasisimpleFactorization
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every radical supplement moves the seed, conditional on the earlier 13.6.6. -/
theorem replacement_moves_of_characteristic_two {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦)
    (T : Sylow 2 G) (z v : G)
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hvT : v ∈ T) (hv : v ≠ 1) (hv2 : v ^ 2 = 1)
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hchar : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hcore : ∀ K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v),
      Tv (T : Subgroup G) v ≤ normalizer (K : Set G) →
      ¬ K ≤ centralizer ({z} : Set G) → (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥)
    (K K₁ : Subgroup G)
    (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hm : ¬ K ≤ centralizer ({z} : Set G))
    (hgen : (solvableRadical K).map K.subtype ⊔ K₁ = K) :
    ¬ K₁ ≤ centralizer ({z} : Set G) := by
  let S := Tv (T : Subgroup G) v
  let H := K ⊔ S
  have hHG : H ≤ Gv v := sup_le hK.1 inf_le_right
  have hzmem := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
  have hzS : z ∈ omegaOneCenterAmbient S := (mem_omegaOneCenterAmbient_iff S z).mpr
    ⟨⟨hzmem.1, mem_centralizer_singleton_iff.mpr (hzmem.2.2 v hvT).symm⟩,
      hzmem.2.1, fun s hs => hzmem.2.2 s hs.1⟩
  have hzH : z ∈ H := (show S ≤ H from le_sup_right) ((mem_omegaOneCenterAmbient_iff S z).mp hzS).1
  let W := seedSpan H z hzH
  let : IsElementaryAbelian 2 W := seedSpan_elementary (T : Subgroup G) z v
    hSylow hzS hchar H hHG hzH
  obtain ⟨P, hP⟩ := hK.2.2.1
  have hpc : (P : Subgroup H) ≤ centralizer ({⟨z, hzH⟩} : Set H) := by
    intro p hp
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact hzmem.2.2 p ((hP ▸ mem_map_of_mem H.subtype hp).1)
  have hwcore : pCore 2 (ActionQuotient W) = ⊥ := seedSpan_twoCore H z hzH P hpc
  let B := K.subgroupOf H
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hS)
  have hBP : B ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, hP,
      ← MonoidHom.range_eq_map, range_subtype]
  have hHsq : IsSQTK 𝒦 H := (IsSQTK.equiv (subgroupOfEquivOfLe hHG)).mp
    ((hG.involution_centralizer_sqtk (orderOf_eq_prime hv2 hv)).subgroup (H.subgroupOf (Gv v)))
  have hquasi : IsQuasisimple (B.map (actionMk W)) := by
    by_contra hnq
    have hfact := (AdequateFactorization.thompson_factorization classification hHsq P B W
      hK.2.1 hBP hwcore hnq).2
    obtain ⟨K₂, hloc, hinv, hmove, hnorm⟩ :=
      moving_thompson_replacement T z v hvT hv K hK hS hm hzH P hP hfact
    let C : Subgroup S := elementaryAbelianMaxJ ⊤
    let : C.Characteristic := elementaryAbelianMaxJ_top_characteristic
    exact not_normalizes_characteristic_of_twoCore_eq_bot T v K₂ hidx C
      (thompson_centralizer_ne_bot T v hvT hv) (hcore K₂ hloc hinv hmove)
      (by rwa [thompson_centralizer_map])
  exact replacement_moves_of_quasisimple_action H K K₁ z hzH le_sup_left hgen hm hquasi

/-- Application to the actual marked source configuration and literal
normalizer residual. The involution and Sylow premises come from the marking
and local reductions. The earlier characteristic-two result remains explicit. -/
theorem normalizer_residual_moves_of_marked_setup {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦)
    (T : Sylow 2 G) (L M V V₁ V₂ : Subgroup G)
    (f : A5Module.FlagMarking T L V V₁ V₂) (hVT : V ≤ (T : Subgroup G))
    (d : LocalReductions T L M V (A5Module.markedZ f.module) (A5Module.markedV f.module))
    (hidx : (Tv (T : Subgroup G) (A5Module.markedV f.module)).relIndex (T : Subgroup G) = 2)
    (hchar : generalizedFitting (Gv (A5Module.markedV f.module)) =
      pCore 2 (Gv (A5Module.markedV f.module)))
    (hcore : ∀ K ∈ Chapter1.LIn (Gv (A5Module.markedV f.module))
        (Tv (T : Subgroup G) (A5Module.markedV f.module)),
      Tv (T : Subgroup G) (A5Module.markedV f.module) ≤ normalizer (K : Set G) →
      ¬ K ≤ centralizer ({A5Module.markedZ f.module} : Set G) →
        (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥)
    (K K₁ : Subgroup G)
    (hK : K ∈ Chapter1.LIn (Gv (A5Module.markedV f.module))
      (Tv (T : Subgroup G) (A5Module.markedV f.module)))
    (hS : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤ normalizer (K : Set G))
    (hm : ¬ K ≤ centralizer ({A5Module.markedZ f.module} : Set G))
    (hgen : (solvableRadical K).map K.subtype ⊔ K₁ = K)
    (C : Subgroup (Tv (T : Subgroup G) (A5Module.markedV f.module)))
    (hres : K₁ = (solvableResidual
      (K ⊓ normalizer (C.map (Tv (T : Subgroup G) (A5Module.markedV f.module)).subtype : Set G) : Subgroup G)).map
        (K ⊓ normalizer (C.map (Tv (T : Subgroup G) (A5Module.markedV f.module)).subtype : Set G)).subtype) :
    ¬ (solvableResidual
      (K ⊓ normalizer (C.map (Tv (T : Subgroup G) (A5Module.markedV f.module)).subtype : Set G) : Subgroup G)).map
        (K ⊓ normalizer (C.map (Tv (T : Subgroup G) (A5Module.markedV f.module)).subtype : Set G)).subtype ≤
      centralizer ({A5Module.markedZ f.module} : Set G) := by
  have hvT : A5Module.markedV f.module ∈ T := hVT (A5Module.map_mem f.module _)
  have hv2 : A5Module.markedV f.module ^ 2 = 1 := by
    change (f.module.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v)) ^ 2 = 1
    rw [← map_pow]
    have he : (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1 := by
      decide +kernel
    rw [he, map_one]
  rw [← hres]
  exact replacement_moves_of_characteristic_two hG classification T _ _ f.z_central
    hvT (A5Module.markedV_ne_one f.module) hv2 ⟨d.centralizerSylow, d.sylow_image⟩
    hidx hchar hcore K K₁ hK hS hm hgen

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement

end

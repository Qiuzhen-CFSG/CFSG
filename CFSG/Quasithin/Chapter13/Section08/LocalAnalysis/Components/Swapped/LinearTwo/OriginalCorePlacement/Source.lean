module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalCorePlacement.BorelAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalOrthogonal
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.SourceOrbit

/-!
# The original marked parabolic-core containment

OriginalBorel constructs the marked binary Borel and proves n = 2 and
L₁ = O²(B₀). OriginalResidual identifies K₀ with O^{3′}(H), so its
star image is normal. The product coordinates and the two-group supplement
make that orbit self-centralizing. The Borel-action calculation therefore
gives O₂(L₁T)* ≤ K₀* through the literal H/O₂(H) map.

Applying the original critical-pair contradiction excludes the orthogonal
orbit, with its actual module identification as the only additional input.
The final adapter also discharges the placement premise in the existing
cross-factor/orthogonal dichotomy. Module recognition and discharge of the
earlier source hypotheses remain with qt-d-138-swapped-linear-two-source.

Source: Aschbacher--Smith, 13.8.16(1), printed pp.952--953 (PDF pp.969--970).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving

/-- The marked relative two-core is contained in the exchanged component orbit
after applying the original star map. No actor-placement premise is used. -/
theorem parabolic_core_star_le_orbit {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n)) :
    Source.starImage H ((one L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) ≤
      Source.starImage H (conjugateSpanBy K (T : Subgroup G)) := by
  obtain ⟨t, ht, htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  have hi := moving_index d h hF9all hcentral hcomm hsource hH hKH hK hmoving
  obtain ⟨hKO, hTH, e, S, _, _, _, _, _, hLB, _, hPB, _, _, _, _,
    _, hn2, hres, _⟩ :=
    borel_diagonal d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ht htn
  have horbit := orbit_eq_two_conjugates H K T hKH hTH hi ht htn
  have hLorbit : one L T V₁ ≤ conjugateSpanBy K (T : Subgroup G) := by
    rw [horbit]
    exact hLB.trans (borelLift_le H (K ⊔ K.conjBy t) hKO _)
  have hC := ModuleAlternatives.FFFactors.source_orbit_centralizer H K (one L T V₁)
    (T : Subgroup G) hgen.symm hLorbit T.isPGroup' hmodel
    (e.symm.trans (MulEquiv.subgroupCongr (congrArg (Source.starImage H) horbit.symm)))
  rw [horbit] at hC ⊢
  have hres3 := threeResidual d h hF9all hcentral hcomm hsource hH hKH hK hmoving hn hmodel
  rw [horbit] at hres3
  have hrel : (K ⊔ K.conjBy t).subgroupOf H = primeToResidual 3 H := by
    rw [← hres3]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  let : (Source.starImage H (K ⊔ K.conjBy t)).Normal := by
    change (((K ⊔ K.conjBy t).subgroupOf H).map
      (QuotientGroup.mk' (pCore 2 H))).Normal
    rw [hrel]
    exact Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let := (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  have hP := SourceActions.normalizes_orbit H K hKH hi (hTH ht) htn
  apply OriginalCorePlacement.star_core_le H (K ⊔ K.conjBy t) (one L T V₁)
    (one L T V₁ ⊔ (T : Subgroup G)) hKO hH.1.2 (hH.1.2.trans hP) e S
    (by simpa [hn2] using hmodel) hC le_sup_left hLB hPB hres

open ModuleAlternatives
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

/-- Exclude the actual orthogonal module using the constructed parabolic-core placement. -/
theorem false_of_orthogonal_orbit {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (horth : HasOrthogonalFourOrbit ρ
      (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))) : False := by
  exact false_of_orthogonal_orbit_of_core_placement d h hF9all hcentral hcomm hsource
    hH hKH hK hmoving hn hmodel ρ hρ horth
    (parabolic_core_star_le_orbit d h hF9all hcentral hcomm hsource
      hH hKH hK hgen hmoving hn hmodel)

/-- Both actual module alternatives are excluded without an extra placement premise. -/
theorem false_of_module_alternatives {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G))
    (halternative : HasCrossFactorQuotient ρ (Source.starImage H K)
        (Source.starImage H (K.conjBy t)) ∨
      HasOrthogonalFourOrbit ρ (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))) :
    False := by
  exact false_of_module_alternatives_of_core_placement d h hF9all hcentral hcomm hsource
    hH hKH hK hmoving hn hmodel hgen ρ hρ ht htn halternative
    (fun _ => parabolic_core_star_le_orbit d h hF9all hcentral hcomm hsource
      hH hKH hK hgen hmoving hn hmodel)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original

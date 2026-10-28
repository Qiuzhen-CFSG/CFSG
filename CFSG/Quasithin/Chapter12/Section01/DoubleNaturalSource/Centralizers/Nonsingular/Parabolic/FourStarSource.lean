module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FourStarModels
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.JankoSource

/-!
# The original nonsingular Sylow and the reduced star models

In degree four the adapted point Sylow is Sylow in C_G(w). Its intersection
with the relatively normal containing component maps to a full Sylow of
K*. This Sylow lies in the literal C_M(w)-intersection image. The original
perfect residual retains its PSL3(2) quotient through the solvable star
kernel. Properness of the marked intersection and the proved B.5 catalogue
therefore leave only A7, SL4(2), and SL5(2).

The final theorem applies this reduction to the nonsingular-centralizer,
global-r and degree-five zeroth-closure conclusions. The full local action
must still exclude A7 and SL4(2), identify the SL5(2) parabolic, and prove
its fixed-space conclusion. The degree-five nonnormal branch and ordinary
J4 exclusion also remain with qt-d-double-natural-centralizers. Independent
pure fusion and corrected MS retain their existing producers and final
discharge at qt-d-1222-double-natural. No full C.2.7 Source is assumed here.
Source: Aschbacher--Smith 12.1.1--3, printed pp.788--789.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original point Sylow maps to a full Sylow in the actual star intersection.
Only normality relative to C_G(w) is used. -/
theorem doubleNatural_four_adapted_C27_star_sylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        ∃ P : Sylow 2 (starImage K Q K),
          (P : Subgroup _) ≤ (starM K Q (B.localPointCentralizer w)).subgroupOf (starImage K Q K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hn hi
  let H := B.pointCentralizer w
  let K₀ := K.subgroupOf H
  let : K₀.Normal := hn
  obtain ⟨P₀,hP₀⟩ := D.doubleNatural_four_adapted_ambientSylow h B S w hw
  obtain ⟨P₁,hP₁⟩ := P₀.exists_sylow_map_eq_inf_of_normal K₀
  let eK := subgroupOfEquivOfLe hi.component.1
  let P₂ := P₁.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hP₂ : (P₂ : Subgroup K).map K.subtype = B.pointSylow w ⊓ K := by
    change ((P₁ : Subgroup K₀).map eK.toMonoidHom).map K.subtype = _
    rw [map_map]
    have he : K.subtype.comp eK.toMonoidHom = H.subtype.comp K₀.subtype := rfl
    rw [he,←map_map,hP₁,map_inf _ _ _ H.subtype_injective,hP₀,
      map_subgroupOf_eq_of_le hi.component.1]
  refine ⟨P₂.mapSurjective (toStarImage_surjective K Q),?_⟩
  rintro _ ⟨k,hk,rfl⟩
  have hkP : (k : G) ∈ B.pointSylow w := (hP₂ ▸ mem_map_of_mem K.subtype hk).1
  have hPM : B.pointSylow w ≤ B.localPointCentralizer w :=
    le_inf (inf_le_left.trans D.sylow_normalizes_component) inf_le_right
  exact mem_map_of_mem (QuotientGroup.mk' (starKernel K Q))
    (show (k : G) ∈ B.localPointCentralizer w ⊓ K from ⟨hPM hkP,k.property⟩)

/-- The genuine degree-four nonnormal input has only A7, L4(2), or L5(2)
as its star component. Every other B.5 model is excluded using the actual Sylow and residual. -/
theorem doubleNatural_four_adapted_C27_star_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        Nonempty (starImage K Q K ≃* alternatingGroup (Fin 7)) ∨
          Nonempty (starImage K Q K ≃* SL(4,ZMod 2)) ∨
          Nonempty (starImage K Q K ≃* SL(5,ZMod 2)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hn hRK hi
  let R := B.pointResidual w
  let M := B.localPointCentralizer w
  have hRM : R ≤ M := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  let := (S.nonsingular_residual_local_cComponent w hw.nonsingular).perfect
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRM).toMonoidHom) (subgroupOfEquivOfLe hRM).surjective
  let : IsQuasisimple (K ⧸ pCore 2 K) := hi.quasisimple
  let : Group.IsPerfect (starImage K Q K) :=
    Group.IsPerfect.ofSurjective (coreToStar_surjective hi.normalizes)
  let f := (toStarImage K Q).comp (inclusion hRK)
  let : Group.IsSolvable f.ker := six_star_map_ker_solvable hi hRK
  obtain ⟨e⟩ := (S.nonsingular_residual_kernel_and_quotient w hw.nonsingular).2
  obtain ⟨P,hP⟩ := D.doubleNatural_four_adapted_C27_star_sylow h B S w hw K hn hi
  apply Nonsingular.four_star_models e f P
    ((starM K Q M).subgroupOf (starImage K Q K)) hP _
    (starM_subgroupOf_ne_top hi) (star_model_from_source hi)
  rintro _ ⟨r,rfl⟩
  exact mem_map_of_mem (QuotientGroup.mk' (starKernel K Q))
    (show (r : G) ∈ M ⊓ K from ⟨hRM r.property,hRK r.property⟩)

/-- Apply the reduced degree-four star catalogue to the actual nonsingular
centralizer and zeroth-closure consumer. Degree five and the J4 exclusion
retain their original source obligations. -/
theorem doubleNatural_nonsingular_controls_of_jankoFour_star_models_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) → False) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w < K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        KernelConclusion K Q → OffenderConclusion K Q →
        ((starImage K Q (B.pointResidual w)).subgroupOf
          (starM K Q (B.localPointCentralizer w))).Normal →
        Nonempty (((starImage K Q (B.pointResidual w)) ⧸
          pCore 2 (starImage K Q (B.pointResidual w))) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2)) →
        (n = 5 ∨ (n = 4 ∧
          (Nonempty (starImage K Q K ≃* alternatingGroup (Fin 7)) ∨
            Nonempty (starImage K Q K ≃* SL(4,ZMod 2)) ∨
            Nonempty (starImage K Q K ≃* SL(5,ZMod 2))))) →
        B.pointResidual w ≤ centralizer ((starV K Q).map (K ⊔ Q).subtype ⊓
          centralizer (B.pointSylow w : Set G) : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hj hp
  apply D.doubleNatural_nonsingular_controls_of_jankoFour_C27_of_many h hmany B hj
  intro S w hw hc hn hout Q K hKn hRK hi hk ho hAn hAq
  apply hp S w hw hc hn hout K hKn hRK hi hk ho hAn hAq
  rcases B.degree with hn | hn
  · subst n
    exact .inr ⟨rfl,D.doubleNatural_four_adapted_C27_star_models h B S w hw K hKn hRK.le hi⟩
  · exact .inl hn
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

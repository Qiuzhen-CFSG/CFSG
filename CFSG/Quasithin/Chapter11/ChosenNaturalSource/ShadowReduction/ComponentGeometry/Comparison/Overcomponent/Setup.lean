module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Reduction
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ReducedDetection
public import CFSG.Quasithin.Chapter3.Section02.SourceSelection
public import Theory.GroupTheory.ReducedNormal.SylowCenter

/-!
# The actual reduced module of a point overcomponent

The original point lies in the omega-center of the fixed Sylow subgroup.
Characteristic two and reduced-subgroup inheritance put it in R₂(JT) for
each local overcomponent J. A proper overcomponent moves this point, so
its intrinsic module is nonzero. Thus a quasisimple maximal overcomponent
has an actual Fundamental Setup, without assuming any FF conclusion.

The same point inclusion rules out the radical-supplement embedding once
the maximal-local specialization of 3.2.14 is supplied. That earlier
implication is owned by qt-d-1222-comparison-nonquasisimple and discharged
by qt-d-1222-shadow-component-comparison. The embedding classification
and the alternatives of 7.0.1 are separate source obligations.

Source: Aschbacher--Smith, 11.4.2, printed p.776; B.2.14 and A.4.11,
printed pp.78 and61. All radicals and reduced subgroups use literal
subgroup inclusions into the original ambient group.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

/-- R₂(JT), embedded into the original ambient group. -/
def reducedIn (T : Sylow 2 G) (J : Subgroup G) : Subgroup G :=
  (reducedTwoSubgroup (J ⊔ (T : Subgroup G) : Subgroup G)).map
    (J ⊔ (T : Subgroup G)).subtype

/-- The solvable radical of J, with its actual ambient inclusion. -/
def radicalIn (J : Subgroup G) : Subgroup G := (solvableRadical J).map J.subtype

/-- The precise shared 3.2.14 implication used in this branch. Its proof
belongs to the nonquasisimple owner, not to the embedding classification. -/
def MaximalRadicalCentralization (T : Sylow 2 G) : Prop :=
  ∀ J ∈ Chapter1.LStar G (T : Subgroup G),
    ¬ IsQuasisimple (J ⧸ pCore 2 J) →
    radicalIn J ≤ centralizer (reducedIn T J : Set G)

/-- The specified point lies in the literal R₂(JT) for every local J. -/
theorem point_mem_reduced (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) : E.z ∈ reducedIn T J := by
  let A := J ⊔ (T : Subgroup G)
  have hzT : E.z ∈ (T : Subgroup G) := D.le_sylow (E.V₁_le h.point_mem)
  have hzA : E.z ∈ A := (show (T : Subgroup G) ≤ A from le_sup_right) hzT
  let zA : A := ⟨E.z, hzA⟩
  let P : Sylow 2 A := T.subtype le_sup_right
  have hchar : HasCharacteristicTwo A := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (E.input.source.simpleQTKE.evenCharacteristic T)
      ⟨hJ.2.2, show (T : Subgroup G) ≤ A from le_sup_right⟩)
  have hzP : zA ∈ omegaCenterIn (P : Subgroup A) := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hzT, ?_, ?_⟩
    · intro t ht
      exact Subtype.ext (h.point_fixed t ht)
    · apply Subtype.ext
      let := D.elementary
      exact elemPow_eq_one_of_isElementaryAbelian E.z (E.V₁_le h.point_mem)
  exact mem_map_of_mem A.subtype ((sylow_omegaCenter_le_reduced P hchar) hzP)

/-- Point movement is already movement of the actual reduced subgroup. -/
theorem reduced_action_ne_bot (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J) :
    ⁅reducedTwoSubgroup (J ⊔ (T : Subgroup G) : Subgroup G),
      J.subgroupOf (J ⊔ (T : Subgroup G))⁆ ≠ ⊥ := by
  intro he
  apply h.proper_overcomponent_moves_point hJ hlt
  obtain ⟨z, hz, hez⟩ := point_mem_reduced h hJ
  intro j hj
  apply mem_centralizer_singleton_iff.mpr
  have hc := commutator_eq_bot_iff_le_centralizer.mp he hz
    (⟨j, (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left) hj⟩ :
      ↥(J ⊔ (T : Subgroup G))) hj
  have hcG : j * (z : G) = (z : G) * j := congrArg Subtype.val hc
  change (z : G) = E.z at hez
  simpa only [hez] using hcG

/-- A proper overcomponent belongs to the faithful local family. No FF
module, irreducibility or classification alternative is assumed. -/
theorem faithful (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J) :
    ChapterA.Section04.IsFaithfulSignalizerType J := by
  refine ⟨Chapter1.Section02.Adequate.mem_L_isSignalizerType T
    (E.input.source.simpleQTKE.evenCharacteristic T) hJ, ?_⟩
  exact Chapter3.RadicalCentralization.intrinsicModule_ne_bot_of_reduced_action
    J (J ⊔ (T : Subgroup G)) le_sup_left hJ.1.subnormal
    (Chapter1.Section02.Adequate.mem_L_isPPerfect hJ) (reduced_action_ne_bot h hJ hlt)

/-- Select the genuine homogeneous constituent for a quasisimple maximal
overcomponent. This is the full input on which 7.0.1 must be applied. -/
theorem exists_fundamentalSetup (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hlt : E.Kz < J)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) :
    Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T J) :=
  Chapter3.Section02.source_exists_fundamentalSetup E.input.source.simpleQTKE T J hJ
    (faithful h hJ.1 hlt) hq

/-- Centralization of the actual reduced subgroup implies fixation of z. -/
theorem radical_centralizes_point (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hc : radicalIn J ≤ centralizer (reducedIn T J : Set G)) :
    radicalIn J ≤ Gz E := by
  intro r hr
  exact mem_centralizer_singleton_iff.mpr (hc hr E.z (point_mem_reduced h hJ)).symm

/-- The nilpotent-extension embedding has a radical supplement. When
3.2.14 centralizes the reduced module, that supplement cannot enlarge Kz. -/
theorem eq_of_radical_supplement (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hle : E.Kz ≤ J)
    (hsplit : J = E.Kz ⊔ radicalIn J)
    (hc : radicalIn J ≤ centralizer (reducedIn T J : Set G)) : J = E.Kz := by
  apply h.overcomponent_eq_of_centralizes_point hJ hle
  rw [hsplit]
  exact sup_le h.point_component.1 (radical_centralizes_point h hJ hc)

/-- The shared maximal-local radical implication closes the proper
radical-supplement row, on the literal original point component. -/
theorem not_radical_supplement (h : EarlierGeometry E)
    (hrad : MaximalRadicalCentralization T) {J : Subgroup G}
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hlt : E.Kz < J)
    (hnq : ¬ IsQuasisimple (J ⧸ pCore 2 J)) : J ≠ E.Kz ⊔ radicalIn J := by
  intro hsplit
  exact hlt.ne' (eq_of_radical_supplement h hJ.1 hlt.le hsplit (hrad J hJ hnq))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent

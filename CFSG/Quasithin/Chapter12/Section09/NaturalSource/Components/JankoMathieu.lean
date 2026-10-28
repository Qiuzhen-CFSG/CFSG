module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Janko
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu

/-!
# Excluding the Mathieu local placement of the original J₄ plane image

The original quotient JT/O₂(JT), its full Sylow image, and both nested
local components are retained. For every actual marking as J₄, the
plane image and Sylow cannot both lie in the native Mathieu local
subgroup. Its literal M₂₄ quotient would force the plane-component
quotient to be PSL₄(2) or M₂₄, and the original full S₃ plane action
already excludes both.

The remaining J₄ placement and component cases belong to the natural
source assembly; this module does not assert ComponentInput.
Source: Aschbacher--Smith 12.9.3, printed pp.858--859.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Subgroup Theory.GroupTheory
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
local notation "M" => Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four

/-- The actual plane image and full quotient Sylow cannot lie together in
any marked copy of the native Mathieu local subgroup of J4. -/
theorem five_janko_plane_not_mathieu_local
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model))
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDn : (D.subgroupOf (F.Gi 2)).Normal)
    (hLD : F.Li L 2 < D) (hDJ : D < J) :
    let X := J ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 X)
    let B := (D.subgroupOf X).map q
    let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 X))
    ∀ e : (X ⧸ pCore 2 X) ≃* Janko4.Model,
      ¬ (B.map e.toMonoidHom ≤ M ∧ (S : Subgroup _).map e.toMonoidHom ≤ M) := by
  let X := J ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 X)
  let B := (D.subgroupOf X).map q
  let A := ((F.Li L 2).subgroupOf X).map q
  let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 X))
  change ∀ e : (X ⧸ pCore 2 X) ≃* Janko4.Model,
    ¬ (B.map e.toMonoidHom ≤ M ∧ (S : Subgroup _).map e.toMonoidHom ≤ M)
  intro e ⟨hBM,hSM⟩
  have hDX : D ≤ X := hDJ.le.trans le_sup_left
  have hm : LargePointModel (J ⧸ pCore 2 J) := Or.inr (Or.inr hJm)
  have hmodels := five_quotient_local_models h earlier F J D hJ hLJ hm hD hDJ.le
  have hn : (S : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (B : Set _) := by
    have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) :=
      (F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hD.1).mp hDn)
    have hnX : (T : Subgroup G).subgroupOf X ≤ normalizer (D.subgroupOf X : Set X) := by
      rw [←subgroupOf_normalizer_eq hDX]
      exact comap_mono hTD
    exact (map_mono (f := q) hnX).trans ((D.subgroupOf X).le_normalizer_map q)
  have hk : IsPGroup 2 (q.subgroupMap (D.subgroupOf X)).ker := by
    rw [ker_subgroupMap]
    have hq : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    exact hq.comap_subtype
  let d := subgroupOfEquivOfLe hDX
  let a := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans
    ((q.subgroupMap (D.subgroupOf X)).pCoreQuotientEquiv
      (q.subgroupMap_surjective _) hk)
  have hquasi : IsQuasisimple (B ⧸ pCore 2 B) :=
    (five_sporadic_plane_component_quasisimple h F J D (Or.inr hJm) hD hLD.le hDJ.le).of_mulEquiv a
  have hXH : X ≤ F.H := sup_le hJ.1 (F.invariant 1)
  have hsqX : IsSQTK KnownSimple.IsKnownSimple X :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hXH)).mp
      ((h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 1 (by decide))).subgroup
        (X.subgroupOf F.H))
  have hsqQ := ChapterE.Structure.sqtk_two_quotient hsqX (pCore 2 X) pCore_isPGroup
  have hlt : A < B :=
    (five_quotient_overgroup_chain h earlier F J D hJ hLJ hJn hD hDn hLD hDJ).2.2.2.1
  rcases ChapterA.Section03.SourceEmbeddings.JankoMathieu.strict_three_pair_map_le_max1_models
      e hsqQ S hmodels.2.1 hmodels.2.2.1 hlt hn hquasi hmodels.2.2.2.2.1 hBM hSM with hb | hb
  · exact plane_component_not_linear h F D hD hDn (Or.inl rfl) (hb.of_mulEquiv a)
  · exact plane_component_not_mathieu h F D hD hDn ⟨a.trans hb.some⟩
end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components

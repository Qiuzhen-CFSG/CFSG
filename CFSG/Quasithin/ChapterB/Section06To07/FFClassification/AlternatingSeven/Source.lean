module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSeven.Ambient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource

/-!
# The two original A₇ actor rows in B.6.9 are excluded

The generalized Fitting subgroup of the actual normal offender supplement
embeds as the two-residual. Its A₇ marking contradicts minimal parabolicity
using the intrinsic pair of Sylow overgroups. Apply this to the natural S₇
row's marked alternating subgroup and the exceptional four-dimensional A₇
row. The original moved central quotient is retained, with no extra condition
on the module centralizer.

Source: Aschbacher–Smith B.5.1 and B.6.9, pp.99–103 and116.
-/


public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

theorem source_quasisimple_alternatingSeven_excluded
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (e : generalizedFitting Y ≃* alternatingGroup (Fin 7)) : False := by
  have he := (source_quasisimple_fitting_eq_residual T hP Y hgen hq).1
  let L := (generalizedFitting Y).map Y.subtype
  have hL : L = pResidual 2 G := he
  let : L.Normal := hL ▸ (inferInstance : (pResidual 2 G).Normal)
  let eL : L ≃* alternatingGroup (Fin 7) :=
    ((generalizedFitting Y).equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e
  have hg : L ⊔ (T : Subgroup G) = ⊤ := by rw [hL]; exact pResidual_sup_sylow_eq_top T
  exact not_minimalParabolic_of_alternatingSeven_supplement T L eL hg hP

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem source_quasisimple_symmetricSeven_excluded
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action) (generalizedFitting Y)
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) : False :=
  source_quasisimple_alternatingSeven_excluded T hP Y hgen hq e.subgroupEquiv

/-- The original offender supplement cannot have the actor of either A₇ source row. -/
theorem source_offender_quasisimple_not_alternatingSeven [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ))) :
    ¬ Nonempty (generalizedFitting (offenderSubgroup ρ) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  let := offenderSubgroup_normal ρ
  exact source_quasisimple_alternatingSeven_excluded T hP _
    (offender_generation T hP ρ hff hcore).2 hq e

/-- Both the natural S₇ and exceptional four-dimensional A₇ markings are excluded
on the literal B.5.1 moved central quotient of the original offender group. -/
theorem source_offender_quasisimple_alternatingSeven_rows_excluded [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    ¬ Nonempty (MarkedActionEquiv c.sectionData.action (offenderSubgroup c.sectionData.action)
      (generalizedFitting (offenderSubgroup ρ))
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) ∧
    ¬ Nonempty (generalizedFitting (offenderSubgroup ρ) ≃* alternatingGroup (Fin 7)) := by
  have hn := source_offender_quasisimple_not_alternatingSeven ρ T hP hff hcore hq
  exact ⟨fun ⟨e⟩ => hn ⟨e.subgroupEquiv⟩, hn⟩
end CFSG.Quasithin.ChapterB

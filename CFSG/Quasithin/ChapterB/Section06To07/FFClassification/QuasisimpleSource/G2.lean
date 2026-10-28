module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.G2
/-!
# Excluding both original quasisimple G2 rows

The actual quasisimple fitting subgroup of the offender supplement embeds
as the ambient two-residual. Both full G2 and the binary derived G2 group
have two intrinsic Sylow-invariant parabolics, contradicting the original
minimal parabolic. The final consumer keeps the two literal B.4.2 markings
on the B.5.1 central quotient, including the proper binary derived subgroup.

Source: Aschbacher–Smith B.6.9 and E.2.3, printed pp.116 and 216–217.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]
/-- A full G2 group mark is impossible on the original quasisimple fitting subgroup. -/
theorem source_quasisimple_g2_excluded
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : generalizedFitting Y ≃* Atlas.G2.Model F) : False := by
  have he := (source_quasisimple_fitting_eq_residual T hP Y hgen hq).1
  let L := (generalizedFitting Y).map Y.subtype
  have hL : L = pResidual 2 G := he
  let : L.Normal := hL ▸ (inferInstance : (pResidual 2 G).Normal)
  let eL := ((generalizedFitting Y).equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e
  have hg : L ⊔ (T : Subgroup G) = ⊤ := by rw [hL,pResidual_sup_sylow_eq_top T]
  exact not_minimalParabolic_of_normal_g2 T L hg eL hP

/-- The actual binary derived G2 group mark is also impossible. -/
theorem source_quasisimple_binary_g2_excluded
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (e : generalizedFitting Y ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have he := (source_quasisimple_fitting_eq_residual T hP Y hgen hq).1
  let L := (generalizedFitting Y).map Y.subtype
  have hL : L = pResidual 2 G := he
  let : L.Normal := hL ▸ (inferInstance : (pResidual 2 G).Normal)
  let eL := ((generalizedFitting Y).equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e
  have hg : L ⊔ (T : Subgroup G) = ⊤ := by rw [hL,pResidual_sup_sylow_eq_top T]
  exact not_minimalParabolic_of_normal_binary_g2_derived T L hg eL hP

open QuasisimpleSource
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
/-- Both literal B.4.2 G2 action rows are excluded in the original B.5.1 conclusion. -/
theorem source_offender_quasisimple_g2_exclusions
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    (∀ F : BinaryField, ¬ Nonempty (ActionEquiv
      (c.sectionData.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype) (binaryG2 F))) ∧
    ¬ Nonempty (MarkedActionEquiv c.sectionData.action (offenderSubgroup c.sectionData.action)
      (generalizedFitting (offenderSubgroup ρ)) (g2Natural (ZMod 2))
      (commutator (Atlas.G2.Model (ZMod 2)))) := by
  let := offenderSubgroup_normal ρ
  have hg := (offender_generation T hP ρ hff hcore).2
  constructor
  · rintro F ⟨e⟩
    exact source_quasisimple_g2_excluded T hP _ hg hq e.groupEquiv
  · rintro ⟨e⟩
    exact source_quasisimple_binary_g2_excluded T hP _ hg hq e.subgroupEquiv
end CFSG.Quasithin.ChapterB

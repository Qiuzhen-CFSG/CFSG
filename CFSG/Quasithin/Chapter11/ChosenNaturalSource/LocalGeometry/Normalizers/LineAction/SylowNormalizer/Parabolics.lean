module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.Geometry
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.GroupTheory.UniqueMaximalNormalExtension
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The actual flag residuals give minimal parabolics

The supplied PSL₂(2ⁿ) model is SL₂ in characteristic two. Borel uniqueness
lifts through the literal two-core quotient, since that core lies in the
specified Sylow subgroup. The normal-extension theorem then gives unique
maximality over T inside LᵢT. Consequently the local component enlargement
used in 3.3.16 needs no separate minimal-parabolic premise.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
3.3.10(1) and the first paragraph of 3.3.16, printed pp.588 and 591.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c}

namespace FlagInput
variable (P : FlagInput S f)
include P

/-- The source rank-one Sylow join is genuinely a minimal parabolic. -/
theorem parabolic (i : Fin 2) :
    Order.HasUniqueMaximalOver (T : Subgroup G) (f.Li i ⊔ (T : Subgroup G)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := P.model i
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := S.field.degree)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let eqv := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  obtain ⟨U, hU⟩ := NormalSylowQuotientAction.intersection_sylow T (f.Li i)
    (f.sylow_normalizes_Li i)
  let q := QuotientGroup.mk' (pCore 2 (f.Li i))
  let Uq := U.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (f.Li i)))
  let Uf := Uq.mapSurjective (f := eqv.toMonoidHom) eqv.surjective
  have huf := Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver (F := F) 2 Uf
  have huq : Order.HasUniqueMaximalOver (Uq : Subgroup (f.Li i ⧸ pCore 2 (f.Li i))) ⊤ :=
    hasUniqueMaximalOver_of_surjective eqv.toMonoidHom eqv.surjective
      (by rw [eqv.toMonoidHom.ker_eq_bot eqv.injective]; exact bot_le) huf
  have hu : Order.HasUniqueMaximalOver (U : Subgroup (f.Li i)) ⊤ :=
    hasUniqueMaximalOver_of_surjective q (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal U) huq
  apply hasUniqueMaximalOver_sup_of_normalizes (f.sylow_normalizes_Li i)
  simpa only [hU, subgroupOf_map_subtype, inf_comm] using
    hasUniqueMaximalOver_map_subtype hu

/-- The actual common-normal application has no additional uniqueness premise. -/
theorem enlarged_parabolic_source (A : OddSupplement T) (i : Fin 2) :
    ((f.Li i ⊔ (T : Subgroup G)) ⊔ A.subgroup) ∈ Chapter1.HOver G (T : Set G) :=
  P.enlarged_parabolic_mem_HOver A i (P.parabolic i)

/-- Original source application: a Sylow-normalizer escape produces a proper
normal component enlargement of an actual rank-one flag residual. -/
theorem moved_component_source (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ (i : Fin 2) (K : Subgroup G),
      ¬ A.subgroup ≤ normalizer (f.Li i : Set G) ∧
      Source.NormalComponentIn ((f.Li i ⊔ (T : Subgroup G)) ⊔ A.subgroup) K ∧
      f.Li i < K :=
  P.exists_moved_normal_component A P.parabolic hescape

end FlagInput
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

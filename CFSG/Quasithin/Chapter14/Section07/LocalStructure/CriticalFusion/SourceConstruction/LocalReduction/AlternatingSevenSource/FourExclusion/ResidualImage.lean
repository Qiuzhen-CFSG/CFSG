module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion.Model
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The original residual under the even partition marking

An actual local marking with two-group kernel identifies the image of the
original embedded two-residual with the residual of the even four-plus-three
stabilizer. It therefore identifies the intrinsic two-core quotient with the
model quotient, preserving its order nine and exponent three.

Source: Aschbacher–Smith 14.7.50, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion
open Chapter13.Section08.ComponentSieve.Seven
variable {G : Type*} [Group G] [Finite G]

/-- The literal embedded residual retains the selected even partition image. -/
theorem local_residual_image
    (I J : Subgroup G) (hJI : J ≤ I)
    (f : I →* S7) (hJ : (J.subgroupOf I).map f = Model.P) :
    (((pResidual 2 J).map J.subtype).subgroupOf I).map f = Model.R := by
  have hr := map_embedded_pResidual 2 (J.subgroupOf I) I.subtype
  rw [map_subgroupOf_eq_of_le hJI] at hr
  have hinside : ((pResidual 2 J).map J.subtype).subgroupOf I =
      (pResidual 2 (J.subgroupOf I)).map (J.subgroupOf I).subtype := by
    rw [←hr]
    exact comap_map_eq_self_of_injective I.subtype_injective _
  rw [hinside,map_embedded_pResidual,hJ]
  rfl

/-- The original residual has the actual model two-core quotient. -/
def local_residual_quotient_equiv
    (I J : Subgroup G) (hJI : J ≤ I)
    (f : I →* S7) (hk : IsPGroup 2 f.ker)
    (hJ : (J.subgroupOf I).map f = Model.P) :
    let B := (pResidual 2 J).map J.subtype
    (B ⧸ pCore 2 B) ≃* (Model.R ⧸ pCore 2 Model.R) := by
  let B := (pResidual 2 J).map J.subtype
  have hBI : B ≤ I := (map_subtype_le _).trans hJI
  let fB := f.comp (inclusion hBI)
  have hkB : IsPGroup 2 fB.ker := by
    change IsPGroup 2 (f.ker.comap (inclusion hBI))
    exact hk.comap_of_injective _ (inclusion_injective hBI)
  have him : fB.range = Model.R := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact local_residual_image I J hJI f hJ
  let e := MonoidHom.quotientPCoreEquivOfSurjective fB.rangeRestrict
    fB.rangeRestrict_surjective (show IsPGroup 2 fB.rangeRestrict.ker by
      rwa [MonoidHom.ker_rangeRestrict])
  let a := MulEquiv.subgroupCongr him
  exact e.trans (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))

/-- The literal residual quotient has order nine and exponent three. -/
theorem local_residual_quotient_card_cube
    (I J : Subgroup G) (hJI : J ≤ I)
    (f : I →* S7) (hk : IsPGroup 2 f.ker)
    (hJ : (J.subgroupOf I).map f = Model.P) :
    let B := (pResidual 2 J).map J.subtype
    Nat.card (B ⧸ pCore 2 B) = 9 ∧
      ∀ x : B ⧸ pCore 2 B, x ^ 3 = 1 := by
  let e := local_residual_quotient_equiv I J hJI f hk hJ
  refine ⟨(Nat.card_congr e.toEquiv).trans Model.quotient_card,?_⟩
  intro x
  apply e.injective
  rw [map_pow,map_one]
  exact Model.quotient_cube (e x)

/-- Image, order, and exponent of the original residual under a literal
even partition marking with two-group kernel. -/
theorem local_residual_quotient_of_even_partition
    (I J : Subgroup G) (hJI : J ≤ I)
    (f : I →* S7) (hk : IsPGroup 2 f.ker)
    (hmark : (J.subgroupOf I).map f = Model.P) :
    let B := (pResidual 2 J).map J.subtype
    ((B.subgroupOf I).map f = Model.R) ∧
      Nat.card (B ⧸ pCore 2 B) = 9 ∧
      ∀ x : B ⧸ pCore 2 B, x ^ 3 = 1 :=
  ⟨local_residual_image I J hJI f hmark,
    local_residual_quotient_card_cube I J hJI f hk hmark⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion

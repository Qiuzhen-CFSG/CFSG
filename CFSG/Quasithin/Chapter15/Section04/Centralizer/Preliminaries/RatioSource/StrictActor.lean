module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.Setup
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.StrictAction
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.TwoConjugateRatio

/-!
# The strict dihedral bound in the original intrinsic module

The source witness in H acts through A ≤ O₂(I) ≤ T ≤ M₀. We apply the
strict dihedral cubic theorem directly to the original faithful representation on
V, using its actual quotient map. The equivalence from V viewed inside I
to V inside M₀ identifies both ambient elements. Neither H nor I is
required to normalize V, and no map from Aut_H(V) is assumed.

Source: Aschbacher–Smith, E.2.13(2), E.2.15 and 15.4.2(4), printed pp.224–225, 1156.
The E.2.9/E.2.11 witness construction remains with the outside-core branch.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
open ChapterE.DihedralCubic ChapterE.TwoConjugate
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M₀ M H I : Subgroup G} {V : Subgroup M₀}

/-- The literal E.2.13 actor, with the quotient and module used by `Earlier1542Four`. -/
theorem LocalHypotheses.strict_cubic_actor_of_witness
    (l : LocalHypotheses T M₀ M V)
    (w : TwoConjugateRatio.Witness T M (V.map M₀.subtype) H I) :
    letI := l.reduced.normal
    letI := l.reduced.elementary
    let q := QuotientGroup.mk' (centralizer (V : Set M₀))
    let ρ := Representation.NormalElementaryQuotient.representation V q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let f := actorMap w.geometry (w.sylow_le.trans l.mem_H.2) q
    f.ker = (Z ((V.map M₀.subtype).subgroupOf I) w.conjugator).subgroupOf
      (A ((V.map M₀.subtype).subgroupOf I) ((M ⊓ H).subgroupOf I) w.conjugator) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range < 2 * rank f.range ∧
      actionRatio ρ f.range < 2 ∧ cubicRatio ρ < 2 := by
  let := l.reduced.normal
  let := l.reduced.elementary
  let q := QuotientGroup.mk' (centralizer (V : Set M₀))
  let ρ := Representation.NormalElementaryQuotient.representation V q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let e₀ := V.equivMapOfInjective M₀.subtype M₀.subtype_injective
  let e := (subgroupOfEquivOfLe w.le_I).trans e₀.symm
  let f := actorMap w.geometry (w.sylow_le.trans l.mem_H.2) q
  apply w.geometry.dihedral_cubic_actor_strict w.proper w.fitting w.quotient_card e ρ
    (Representation.NormalElementaryQuotient.representation_injective V q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) f
  intro a v
  apply Subtype.ext
  have he (x : V) : ((e.symm x : I) : G) = (x : M₀) := by
    change ((e₀ x : V.map M₀.subtype) : G) = ((x : M₀) : G)
    rfl
  have hv : ((e v : M₀) : G) = ((v : I) : G) := by
    rw [← he, e.symm_apply_apply]
  rw [he]
  change (((ρ (q (actorIn w.geometry (w.sylow_le.trans l.mem_H.2) a))
    (Additive.ofMul (e v))).toMul : M₀) : G) = _
  rw [Representation.NormalElementaryQuotient.representation_apply]
  change ((a : I) : G) * ((e v : M₀) : G) * ((a : I) : G)⁻¹ = _
  rw [hv]
  rfl

/-- The witness discharges the bound for the exact intrinsic source action. -/
theorem LocalHypotheses.cubicRatio_lt_two_of_witness
    (l : LocalHypotheses T M₀ M V)
    (w : TwoConjugateRatio.Witness T M (V.map M₀.subtype) H I) :
    letI := l.reduced.normal
    letI := l.reduced.elementary
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set M₀)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) < 2 :=
  (l.strict_cubic_actor_of_witness w).2.2.2.2.2

end CFSG.Quasithin.Chapter15.Section04.RatioSource

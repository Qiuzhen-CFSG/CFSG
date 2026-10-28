module
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Residual
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Nonsolvable
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.OffenderSource
/-!
# Nonsolvable alternatives for the actual offender subgroup

The original offender subgroup has the same embedded two-residual as the
ambient minimal parabolic. Nonsolvability makes that residual perfect,
excluding the outer A6–C3 configuration. A solvable offender subgroup would
make the whole actor solvable, so the symmetric-three case is also excluded.
The remaining earlier B.5.6 alternatives retain their complete module data.

Source: Aschbacher–Smith, B.6.9, printed pp.115–116, using B.5.6, p.105.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- Perfection is transported through the literal embedded residual equality. -/
theorem nonsolvable_offender_residual_perfect
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥) :
    Group.IsPerfect (pResidual 2 (offenderSubgroup ρ)) := by
  have he := offender_residual_eq T hP ρ hff hcore
  let : Group.IsPerfect ((pResidual 2 (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype) := by
    rw [he]
    exact minimalParabolic_nonsolvable_residual_perfect T hP hs
  let e := (pResidual 2 (offenderSubgroup ρ)).equivMapOfInjective
    (offenderSubgroup ρ).subtype (offenderSubgroup ρ).subtype_injective
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- The actual offender subgroup cannot have the outer A6–C3 configuration. -/
theorem nonsolvable_offender_not_outerSixThree
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥) :
    ¬ Nonempty (OuterSixThreeShape (offenderSubgroup ρ)) := by
  rintro ⟨c⟩
  exact c.not_perfect_two_residual (nonsolvable_offender_residual_perfect ρ T hP hs hff hcore)

/-- A nonsolvable source has a nonsolvable offender subgroup. -/
theorem nonsolvable_offender_not_solvable
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥) :
    ¬ Group.IsSolvable (offenderSubgroup ρ) := by
  intro hy
  let := hy
  have hr := (offender_generation T hP ρ hff hcore).1
  let : Group.IsSolvable (pResidual 2 G) :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion hr) (inclusion_injective hr)
  let : Group.IsNilpotent (G ⧸ pResidual 2 G) := (isPGroup_quotient_pResidual 2).isNilpotent
  exact hs ((Group.isSolvable_iff_subgroup_quotient (pResidual 2 G)).mpr
    ⟨inferInstance, inferInstance⟩)

/-- The complete earlier classifier leaves exactly these three source branches. -/
theorem nonsolvable_offender_classification
    (earlier : SourceInduction.AdequateClassificationInput.{u,v} K)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hf : Function.Injective ρ)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hcover : Nonempty (SourceInduction.SQTKQuotient K G)) :
    let σ := ρ.comp (offenderSubgroup ρ).subtype
    (IsQuasisimple (generalizedFitting (offenderSubgroup ρ)) ∧
      Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion σ
        (generalizedFitting (offenderSubgroup ρ)))) ∨
      Nonempty (SourceInduction.SourceTwoFactorCase σ) ∨
      Nonempty (SourceInduction.HyperplaneCase σ) := by
  have hn := nonsolvable_offender_not_solvable ρ T hP hs hff hcore
  let : Nontrivial (offenderSubgroup ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr
    (offenderSubgroup_ne_bot_of_ff ρ hff)
  have hc := (offender_restriction_classification ρ earlier hf hcore hcover).of_nontrivial _
  cases hc with
  | quasisimple hq ha => exact Or.inl ⟨hq,⟨ha⟩⟩
  | symmetricThree c =>
      let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
        let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
        apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
        rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
      exact (hn (Group.isSolvable_of_isSolvable_injective
        (f := c.equiv.toMonoidHom) c.equiv.injective)).elim
  | twoFactors c => exact Or.inr (Or.inl ⟨c⟩)
  | outerSixThree c =>
      exact (nonsolvable_offender_not_outerSixThree ρ T hP hs hff hcore ⟨c⟩).elim
  | hyperplane c => exact Or.inr (Or.inr ⟨c⟩)
end CFSG.Quasithin.ChapterB

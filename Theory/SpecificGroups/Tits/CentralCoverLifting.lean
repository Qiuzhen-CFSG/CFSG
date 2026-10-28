module

public import Theory.SpecificGroups.Tits.Presentation
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Parrott relations in perfect central covers of the Tits group

If lifts of the ten named generators satisfy all 37 Parrott relations, the
presentation gives a section of the original projection. Its image supplements
the central kernel. Perfectness forces this image to be the whole covering
group, so the projection is injective. The final theorem applies this argument
to the literal canonical universal projection.

The existence of compatible generator lifts is not asserted here. It is the
remaining central-extension calculation needed for the Tits multiplier, not a
consequence of the order or simplicity of the presented group.

Sources: Parrott, “A Characterization of the Tits' Simple Group” (1972), §5,
p.683, transcribed in `refs/original/n-group-global/parrott-tits-presentation.md`;
Aschbacher–Smith I.1.1 and I.1.3, printed p.407. The relators retain Parrott's
commutator convention `a⁻¹ * b⁻¹ * a * b`.
-/

public section

namespace Tits.CentralCoverLifting

open PerfectCentralCovering
universe u

/-- The homomorphism constructed from the lifted Parrott relations is a
section of the specified projection. -/
theorem lift_section {E : Type u} [Group E] (π : E →* ParrottGroup)
    (g : ParrottGenerator → E) (hrel : SatisfiesParrottRelations g)
    (hproj : ∀ i, π (g i) = parrottGenerator i) :
    π.comp (parrottLift g hrel) = MonoidHom.id ParrottGroup := by
  apply PresentedGroup.ext
  intro i
  exact (congrArg π (parrottLift_generator g hrel i)).trans (hproj i)

/-- Perfectness removes a central kernel once the ten lifts satisfy the
37 relations. No finiteness or quasisimplicity assumption is needed. -/
theorem injective_of_lifted_relations {E : Type u} [Group E] [Group.IsPerfect E]
    (π : E →* ParrottGroup) (hc : π.ker ≤ Subgroup.center E)
    (g : ParrottGenerator → E) (hrel : SatisfiesParrottRelations g)
    (hproj : ∀ i, π (g i) = parrottGenerator i) : Function.Injective π := by
  have hs := lift_section π g hrel hproj
  have hsurj : Function.Surjective (parrottLift g hrel) :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect π (parrottLift g hrel)
      (hs ▸ Function.surjective_id) hc
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  have ha := DFunLike.congr_fun hs a
  have hb := DFunLike.congr_fun hs b
  exact congrArg (parrottLift g hrel) (ha.symm.trans (hxy.trans hb))

/-- The precise application to the canonical universal kernel. The
compatible-lift premise remains a separate mathematical obligation. -/
theorem universalProjection_ker_eq_bot_of_lifts [Group.IsPerfect ParrottGroup]
    (h : ∃ g : ParrottGenerator → UniversalGroup ParrottGroup,
      SatisfiesParrottRelations g ∧
        ∀ i, universalProjection ParrottGroup (g i) = parrottGenerator i) :
    (universalProjection ParrottGroup).ker = ⊥ := by
  obtain ⟨g, hrel, hproj⟩ := h
  exact (universalProjection ParrottGroup).ker_eq_bot_iff.mpr
    (injective_of_lifted_relations _ (universalProjection_ker_le_center _) g hrel hproj)

end Tits.CentralCoverLifting

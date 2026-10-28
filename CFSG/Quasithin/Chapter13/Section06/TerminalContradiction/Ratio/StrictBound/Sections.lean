module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.Source
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Faithful irreducible sections of the terminal quotient action

Starting with the literal action on U_H/V₁, choose an H*-invariant
subquotient on which the perfect generalized Fitting subgroup survives.
The kernel of this section lies in the center of F*(H*). When that center
is trivial, the entire H* action on the section is faithful. Thus passing
to this section preserves the quadratic actor itself, including its rank,
and can only decrease its fixed codimension.

The structural premises refer to the actual residual image.
`residual_quasisimple_of_source` in `Models` supplies quasisimplicity from the
genuine component output; triviality of the center still needs discharge.
No simplicity theorem about an unrelated carrier is used.
The section is irreducible for H*, not yet for its component. The latter
passage and the B.4 classifications remain necessary for the strict bound.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the terminal
paragraph of §13.6, printed p.935 / PDF p.952, and B.4.2/B.4.5, pp.86–87.
The perfect-section existence proof is reused from the general
`exists_irreducible_section_surviving_perfect`; the kernel calculation uses
the proved generalized-Fitting self-centralization theorem.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSections
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound

private theorem faithful_irreducible_section
    {X W : Type*} [Group X] [Finite X]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (hf : Function.Injective ρ)
    (hL : IsQuasisimple (generalizedFitting X))
    (hz : center (generalizedFitting X) = ⊥) :
    ∃ U : Subrepresentation ρ, ∃ N : Subrepresentation U.toRepresentation,
      N.quotientRepresentation.IsIrreducible ∧
      Function.Injective N.quotientRepresentation := by
  let := hL
  have hn : ¬ generalizedFitting X ≤ ρ.ker := by
    intro h
    have hb : generalizedFitting X = ⊥ := le_bot_iff.mp
      (h.trans ((MonoidHom.ker_eq_bot_iff ρ).mpr hf).le)
    let : IsSimpleGroup (generalizedFitting X ⧸ center (generalizedFitting X)) := hL.simple
    have hnt : Nontrivial (generalizedFitting X) :=
      (QuotientGroup.mk'_surjective (center (generalizedFitting X))).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt hb
  obtain ⟨U, N, hi, hn⟩ :=
    Representation.QuadraticFourGroup.exists_irreducible_section_surviving_perfect
      (generalizedFitting X) hn
  refine ⟨U, N, hi, ?_⟩
  have hn' : ¬ generalizedFitting X ≤ N.quotientRepresentation.asGroupHom.ker := by
    intro h
    apply hn
    intro g hg
    exact congrArg Units.val (h hg)
  have hker := kernel_le_fitting_center hL N.quotientRepresentation.asGroupHom hn'
  rw [hz, Subgroup.map_bot] at hker
  intro x y hxy
  exact (MonoidHom.ker_eq_bot_iff _).mp (le_bot_iff.mp hker) (Units.ext hxy)

open Section08

variable {G : Type*} [Group G] [Finite G]
  (H V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
  (hn : H ≤ normalizer (V₁ : Set G))
  (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)

/-- A faithful irreducible H* section exists on the actual terminal module.
The component is precisely the star image of H∞, with the convention fixed
by `terminalResidual_star`. Component irreducibility is not asserted. -/
theorem exists_faithful_irreducible_star_section
    (hfit : generalizedFitting (Source.Hstar H) =
      Source.starImage H (terminalResidual H))
    (hL : IsQuasisimple (Source.starImage H (terminalResidual H)))
    (hz : center (Source.starImage H (terminalResidual H)) = ⊥) :
    ∃ U : Subrepresentation (starRepresentation H V₃ V₁ hn hk),
      ∃ N : Subrepresentation U.toRepresentation,
        N.quotientRepresentation.IsIrreducible ∧
        Function.Injective N.quotientRepresentation := by
  apply faithful_irreducible_section (starRepresentation H V₃ V₁ hn hk)
    (starRepresentation_injective H V₃ V₁ hn hk)
  · exact hfit.symm ▸ hL
  · exact hfit.symm ▸ hz

/-- Restriction and quotient preserve quadraticity and decrease displacement
for the same subgroup of the literal H/O₂(H). No action-image rank is
substituted for the original actor rank. -/
theorem star_section_quadratic_and_fixedCodim
    (U : Subrepresentation (starRepresentation H V₃ V₁ hn hk))
    (N : Subrepresentation U.toRepresentation)
    {A : Subgroup (Source.Hstar H)}
    (hq : IsQuadratic (starRepresentation H V₃ V₁ hn hk) A) :
    IsQuadratic N.quotientRepresentation A ∧
      fixedCodim N.quotientRepresentation A ≤
        fixedCodim (starRepresentation H V₃ V₁ hn hk) A := by
  refine ⟨quadratic_of_equivariant_surjection U.toRepresentation N.quotientRepresentation
    N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation _ U hq), ?_⟩
  exact (Nat.le_add_right _ _).trans
    ((fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A).trans
      (fixedCodim_subrepresentation_le _ U A))

/-- A putative small ratio on U_H/V₁ gives a faithful H*-irreducible section
with the same nontrivial elementary actor and the required displacement
bound. This discharges the first section passage in the terminal reduction. -/
theorem exists_bounded_faithful_irreducible_star_section
    (hfit : generalizedFitting (Source.Hstar H) =
      Source.starImage H (terminalResidual H))
    (hL : IsQuasisimple (Source.starImage H (terminalResidual H)))
    (hz : center (Source.starImage H (terminalResidual H)) = ⊥)
    (hsmall : quadraticRatio (starRepresentation H V₃ V₁ hn hk) ≤ 2) :
    ∃ U : Subrepresentation (starRepresentation H V₃ V₁ hn hk),
      ∃ N : Subrepresentation U.toRepresentation, ∃ A : Subgroup (Source.Hstar H),
        N.quotientRepresentation.IsIrreducible ∧
        Function.Injective N.quotientRepresentation ∧
        IsElementaryTwo A ∧
        IsQuadratic (starRepresentation H V₃ V₁ hn hk) A ∧
        fixedCodim (starRepresentation H V₃ V₁ hn hk) A ≤ 2 * rank A ∧
        IsQuadratic N.quotientRepresentation A ∧
        fixedCodim N.quotientRepresentation A ≤
          fixedCodim (starRepresentation H V₃ V₁ hn hk) A ∧
        fixedCodim N.quotientRepresentation A ≤ 2 * rank A := by
  obtain ⟨U, N, hi, hf⟩ := exists_faithful_irreducible_star_section
    H V₃ V₁ hn hk hfit hL hz
  obtain ⟨A, hA, hq, hc⟩ := (quadraticRatio_le_two_iff _).mp hsmall
  obtain ⟨hqN, hcN⟩ := star_section_quadratic_and_fixedCodim H V₃ V₁ hn hk U N hq
  exact ⟨U, N, A, hi, hf, hA, hq, hc, hqN, hcN, hcN.trans hc⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound

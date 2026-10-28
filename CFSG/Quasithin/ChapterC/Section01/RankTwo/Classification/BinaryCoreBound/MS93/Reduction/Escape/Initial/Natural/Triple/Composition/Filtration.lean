module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Composition.Minimal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Composition.Recognition

/-!
# One natural section with residual-fixed margins

Choose a least invariant subspace moved by the two-residual. Its quotient
by residual-fixed vectors is irreducible and still moving. The fixed-codimension
inequality assigns it the entire rank-one budget, leaving zero endpoint
codimension on the upper quotient. Normal generation modulo the two-group
kernel makes that quotient residual-fixed. Irreducible descent and recognition
identify the literal middle section as natural, allowing the dual marking.

Source: Meierfrankenfeld–Stellmacher (1993), the binary SL₃ case of
(1.4)–(1.5), pp.842–843, used on the dual radius module in (4.3.1)(iii),
p.883. This proves a composition statement only; it does not split extensions
or assert that the two-core fixes the residual moving subspace.
-/

public section

open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple.Composition
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The rank-one binary representation theorem, including both fixed margins
and the equivariant identification of the literal section. -/
theorem exists_residual_filtration (π : G →* BinaryLinearThree.Group)
    (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hc : Nat.card (A.map π) = 2)
    (ρ : Representation (ZMod 2) G E) (hd : fixedCodim ρ A ≤ 1) :
    fixedSpace ρ (pResidual 2 G) = ⊤ ∨
      ∃ F W : Subrepresentation ρ, F ≤ W ∧
        F.toSubmodule ≤ fixedSpace ρ (pResidual 2 G) ∧
        fixedSpace W.quotientRepresentation (pResidual 2 G) = ⊤ ∧
        ∃ a : BinaryLinearThree.Group ≃* BinaryLinearThree.Group,
          Nonempty ((sectionRepresentation ρ F W).Equiv
            ((BinaryLinearThree.W.comp a.toMonoidHom).comp π)) := by
  by_cases hfix : fixedSpace ρ (pResidual 2 G) = ⊤
  · exact Or.inl hfix
  right
  have hn : ¬ (⊤ : Submodule (ZMod 2) E) ≤ fixedSpace ρ (pResidual 2 G) :=
    fun h => hfix (top_unique h)
  obtain ⟨F, W, hFW, hF, hirr, hmove⟩ := exists_minimal_moving_section ρ
    (pResidual 2 G) (Subgroup.isPPerfect_pResidual 2) hn
  let := hirr
  have hne : A.map π ≠ ⊥ := by
    intro hb
    have : Nat.card (A.map π) = 1 := by rw [hb]; exact Nat.card_unique
    omega
  have hpos : 0 < fixedCodim (sectionRepresentation ρ F W) A := by
    by_contra! hz
    have hzero : fixedCodim (sectionRepresentation ρ F W) A = 0 := Nat.eq_zero_of_le_zero hz
    have hfixA := (fixedCodim_eq_zero_iff (sectionRepresentation ρ F W) A).mp hzero
    have hfixP := residual_fixed_of_actor_fixed π hπ hk A hne
      (sectionRepresentation ρ F W) hfixA
    obtain ⟨g, hg, v, hv⟩ := hmove
    exact hv ((show v ∈ fixedSpace (sectionRepresentation ρ F W) (pResidual 2 G)
      by rw [hfixP]; trivial) ⟨g, hg⟩)
  have hsection := fixedCodim_section_add_lower_le ρ F W hFW A
  have hbudget := fixedCodim_quotient_add_subrepresentation_le ρ W A
  have hquot : fixedCodim W.quotientRepresentation A = 0 := by omega
  refine ⟨F, W, hFW, hF, ?_, ?_⟩
  · exact residual_fixed_of_actor_fixed π hπ hk A hne W.quotientRepresentation
      ((fixedCodim_eq_zero_iff W.quotientRepresentation A).mp hquot)
  · apply irreducible_natural π hπ hk A hA hc (sectionRepresentation ρ F W)
    · exact (fixedCodim_section_le ρ F W A).trans hd
    · obtain ⟨g, _, v, hv⟩ := hmove
      exact ⟨g, v, hv⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple.Composition

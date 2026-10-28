module
public import CFSG.Quasithin.ChapterF.Section09.Commutator
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Rank

/-!
# The original F.9.5(2) source input for the component action

The universal F95Two interface is now supplied by the proved F.9 moved-seed
identity on its literal quotient U_H/V₁. Nontriviality of V* discharges
the only core-escape antecedent. The existing representation consumer
therefore has fixed codimension two without a separate F95Two premise.
Source: Aschbacher–Smith F.9.5(2) and13.5.20, printed pp.319,923.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
open Section08.Source Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]

/-- The genuine universally quantified earlier-source implication. -/
theorem source_F95Two : F95Two (G := G) := by
  intro D h hi hstar
  have hn : ¬ D.V ≤ D.QH := by
    intro hc
    apply hstar
    apply bot_unique
    rintro _ ⟨v,hv,rfl⟩
    apply (QuotientGroup.eq_one_iff v).mpr
    obtain ⟨w,hw,he⟩ := hc hv
    exact (show w=v from Subtype.ext he) ▸ hw
  let : (D.V₁.subgroupOf D.UH).Normal := point_normal_in_UH h
  exact h.commutator_image_eq_seed hi hn

/-- The actual binary representation now has fixed codimension two from
F.9.1 and the original source seed index and module order. -/
theorem source_fixedCodim_two {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Quotient (D := D))]
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hc : Nat.card D.V = 16) :
    fixedCodim (representation h) (starImage D.H D.V) = 2 :=
  fixedCodim_two h source_F95Two hi hu hc

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction

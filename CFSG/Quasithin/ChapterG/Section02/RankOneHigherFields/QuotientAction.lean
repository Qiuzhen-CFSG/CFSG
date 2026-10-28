module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.Basic
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.MarkedRoot
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.ProjectiveOrbit
public import Theory.Representation.BinaryOffender.Defs

/-!
# Higher-field quotient recognition and order

`Basic` constructs the elementary quotient S/S₂ and its literal SL₂(F)
conjugation representation. `MarkedRoot` identifies U* with the root group
of the original field line. `ProjectiveOrbit` constructs the equivariant
map on field lines and verifies every hypothesis of G.1.3.

`exists_quotient_natural_decomposition` applies the universally quantified
G.1 recognition implication to this constructed map. It retains the quotient
coordinates, the complement defined by the original g, and an actual equivariant
binary linear decomposition into s natural planes. The marked W/S₂ is the
U*-fixed space; its index and the order of U use the same multiplicity s.

The earlier G.2.2, starred-group, Sylow, Borel and product outputs, and the
universal G.1 recognition implication, remain explicit inputs. Their discharge
belongs to the G.2.3 and G.1 source assembly owners, respectively.

Source: Aschbacher–Smith G.2.3(6–7), printed pp.333–334, PDF pp.344–345,
and G.1.3/G.1.5, printed pp.327–328, PDF pp.338–339.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
open Setup QuotientAction.Projective
universe uG uF
variable {G : Type uG} [Group G] [Finite G]
variable {D : Setup G} {F : Type uF} [Field F] [Finite F]
  {n : ℕ} {g : G} (d : Hypothesis D F n g)

namespace Hypothesis

/-- G.2.3(6–7) on the literal quotient, conditional only on the specified
preceding source outputs and the universally quantified G.1 recognition theorem.
The projective map and direct-sum decomposition are constructed, and the fixed
space, marked index and order formula all use this same action and multiplicity.
The natural number `s` may be zero. -/
theorem exists_quotient_natural_decomposition (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U)
    (hU : Nat.card (D.star D.U) = 2 ^ n)
    (hB : D.star D.L₁ = D.star D.L ⊓ normalizer (D.star D.U : Set D.Star))
    (hsplit : D.S g = WProduct D g)
    (hrecognition : letI := d.field_char_two; RecognitionImplication.{uF, uG} F) :
    letI := d.quotientIntersection_normal hUT hf
    letI := d.quotient_elementary hUT hf hstar hsplit
    letI := d.field_char_two
    ∃ (σ : Representation (ZMod 2) SL(2, F)
        (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))
      (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (D.S₂ g)
        (σ.comp (d.quotientActionProjection hUT hstar)))
      (φ : Point F → Submodule (ZMod 2)
        (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))
      (s : ℕ),
      (∀ x : D.S g, (c.coordinates x).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((D.S₂ g).subgroupOf (D.S g)) x)) ∧
      Criterion σ φ ∧
      φ ⟨d.point, d.point_dimension⟩ = c.imageSpace (D.W g) ∧
      φ (translate (d.quotientActionProjection hUT hstar
        (⟨g, d.g_mem_I_of_star hUT hstar.ge⟩ : D.I g)⁻¹)
        ⟨d.point, d.point_dimension⟩) = c.imageSpace (conjugate (D.W g) g) ∧
      IsCompl (c.imageSpace (D.W g)) (c.imageSpace (conjugate (D.W g) g)) ∧
      NaturalCopies σ s ∧
      c.imageSpace (D.W g) =
        Representation.BinaryOffender.fixedSpace σ (d.quotientRoot hUT hstar) ∧
      (D.S₂ g).relIndex (D.W g) = 2 ^ (n * s) ∧
      Nat.card D.U = 2 ^ (n * (s + 3)) * D.V.relIndex (D.S₂ g) := by
  let := d.quotientIntersection_normal hUT hf
  let := d.quotient_elementary hUT hf hstar hsplit
  let := d.field_char_two
  obtain ⟨σ, c, φ, hcoord, hcriterion, hpoint, htranslate⟩ :=
    d.exists_quotient_projective_map hUT hf hstar hSylow hB hsplit
  obtain ⟨⟨s, hnatural⟩, hfixed⟩ := hrecognition _ σ φ hcriterion
  obtain ⟨e, he⟩ := hnatural
  have hindex := d.quotient_mark_index hUT hf hstar hsplit σ c s e.toEquiv
  refine ⟨σ, c, φ, s, hcoord, hcriterion, hpoint, htranslate,
    (d.quotient_marked_complement hUT hf hstar hsplit σ c).1,
    ⟨e, he⟩, ?_, hindex, d.order_of_natural_indices hUT hf hstar hU s hindex⟩
  ext v
  rw [← hpoint, d.quotientRoot_eq_pointRoot hUT hf hstar hSylow]
  constructor
  · intro hv a
    exact (hfixed ⟨d.point, d.point_dimension⟩ v).mp hv a a.property
  · intro hv
    exact (hfixed ⟨d.point, d.point_dimension⟩ v).mpr (fun a ha => hv ⟨a, ha⟩)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields

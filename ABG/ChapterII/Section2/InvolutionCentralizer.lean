module

public import ABG.ChapterII.Section2.QuasiInvolutionCentralizer
public import ABG.ChapterII.Section2.WreathedInvolutionCentralizer

/-!
# Involution centralizers in QD-groups

In a finite QD-group, the centralizer of every involution is a Q-group
with a semidihedral or wreathed Sylow two-subgroup. The complete original
Q fusion witnesses supplied by the two branches imply the enlarged Q-group
predicate and retain an actual Sylow subgroup of the required shape.

The single ambient involution class places the given involution in a Sylow
center. The quaternion central-product normalizer fixes it, so its outer
automizer index stays six in the centralizer. The complete fusion alternatives
then leave precisely the Q case: the central involution prevents the QD
single-class pattern, while the other excluded cases have outer index two
(or, in the quasi-dihedral D case, only one involution class).
This assembles ABG Chapter II, Section 2, Proposition 1, article p.15
(`refs/latex/alperin-brauer-gorenstein-pages/page-016.tex`), without dropping
either Sylow shape or assuming the narrower original Q definition.
-/

namespace ABG

/-- Every involution centralizer in a QD-group is a Q-group with one of
the two full Sylow shapes specified in ABG II.2 Proposition 1. -/
public theorem qd_involutionCentralizer_isQGroup
    {G : Type*} [Group G] [Finite G] (hG : IsQDGroup G)
    (x : G) (hx : orderOf x = 2) :
    IsQGroup (Subgroup.centralizer {x}) ∧
      ∃ S : Sylow 2 (Subgroup.centralizer {x}),
        Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S := by
  have hfull : IsFullSylowQGroup (Subgroup.centralizer {x}) := by
    rcases hG with ⟨S, T, Q, hf, hQD⟩ | ⟨S, n, U, V, hf, hQD⟩
    · exact quasiQD_involutionCentralizer_isFullSylowQGroup S T Q hf hQD x hx
    · exact wreathedQD_involutionCentralizer_isFullSylowQGroup S n U V hf hQD x hx
  refine ⟨Or.inl hfull, ?_⟩
  rcases hfull with ⟨S, T, Q, hf, _⟩ | ⟨S, n, U, V, hf, _⟩
  · exact ⟨S, Or.inl hf.1⟩
  · exact ⟨S, Or.inr ⟨n, hf.1⟩⟩

end ABG


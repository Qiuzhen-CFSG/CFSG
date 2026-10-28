module
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.LinearThree
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.LinearThree

/-!
# Applying the linear-three rows to the residual-pair comparison

This adapter constructs the literal `LinearThreeInvolutionRows` consumed by
16.4.11 and the centrality comparison in 16.5. Coefficient equivalences take
the linear and derived binary models to the consumer's canonical carriers;
the unitary row keeps the standard Hermitian form and Frobenius clause.
The sole outstanding premise is the degree-two mixed-action marking defined
in `InvolutionResidualRows`. Final assembly must construct that marking.
Source: Aschbacher--Smith 16.1.4, printed p.1171; 16.4.11(2), p.1193.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Matrix.PSL3Even.InvolutionResidualRows
open CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
namespace CFSG.Quasithin.Chapter16.LiePreliminaries

private noncomputable def derivedEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : commutator G ≃* commutator H :=
  ((commutator G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
      rfl))

private noncomputable def binaryEquiv (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (d : ℕ) :
    PSL(d,F) ≃* PSL(d, BinaryGaloisField n) := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (BinaryGaloisField n) := Fintype.ofFinite _
  apply Atlas.fieldEquivPSL d
  apply FiniteField.ringEquivOfCardEq
  simpa only [← Nat.card_eq_fintype_card,
    BenderSuzuki.Converse.card_binaryGaloisField n (Nat.ne_of_gt hn)] using hF

/-- The proved rows discharge the exact later comparison input, once the
remaining small mixed-action marking is supplied. -/
theorem linearThree_comparison_rows_of_four_marking (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hsmall : FourGraphFieldMarking F) :
    LinearThreeInvolutionRows F n := by
  constructor
  intro a ha ho
  rcases involution_cases_of_four_marking hn hF hsmall a ha with hr | hf | hg | hgf
  · obtain ⟨c, _, hc, _⟩ := hr
    exact (ho ((MulAut.congr_inner_iff c a).mp ⟨_,hc⟩)).elim
  · obtain ⟨g, σ, _, _, _, _, m, hm, hnm, hK, ⟨e⟩⟩ := hf
    exact Or.inl ⟨m, hm, hnm,
      ⟨e.trans (derivedEquiv (binaryEquiv (FixedBy.subfield F σ) hm hK 3))⟩⟩
  · obtain ⟨_, _, _, ⟨e⟩⟩ := hg
    exact Or.inr (Or.inl ⟨e.trans (derivedEquiv (binaryEquiv F hn hF 2))⟩)
  · obtain ⟨_, _, _, _, _, _, hsmall | hlarge⟩ := hgf
    · exact Or.inr (Or.inr (Or.inr hsmall))
    · obtain ⟨m, J, hm, hnm, _, hform, hpow, _, hfixed, he⟩ := hlarge
      exact Or.inr (Or.inr (Or.inl ⟨m, hm, hnm, J, hform, hpow, hfixed, he⟩))

/-- The precise table used by the source consumer; the marking premise is
retained so this is not presented as the completed unconditional table. -/
theorem linearThree_comparison_table_of_four_marking
    (hsmall : ∀ (F : Type) [Field F] [Finite F], FourGraphFieldMarking F) :
    LinearThreeInvolutionTable := by
  intro F _ _ n hn hF
  exact linearThree_comparison_rows_of_four_marking F hn hF (hsmall F)

end CFSG.Quasithin.Chapter16.LiePreliminaries

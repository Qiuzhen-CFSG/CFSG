module

public import Theory.Representation.SL3FourNaturalDual.NoFF.RepeatedGraph
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NoFF.GroupReduction

/-!
# The graph obstruction after the faithful FF reduction

For the actual D-invariant section [V,K]/C_[V,K](K), any positive number
of copies of one natural SL₃(4) module is incompatible with a prescribed
linear-graph actor. The group marking may change during recognition; the
universal graph-remarking implication below retains the same ambient actor
and the complete GL₃ correction.

This is the terminal obstruction, not the completed no-FF theorem. Its
`RepeatedNaturalSection` witness must still be constructed from the full
B.5.1 conclusion on J(D,V), after proving that this subgroup satisfies
all source hypotheses. B.4.2 and B.4.5 cannot be applied directly to the
original possibly reducible module. Faithfulness is a separate hypothesis
in that reduction, since `IsFFModule` does not include it.

Source: Aschbacher–Smith, B.4.2 and B.4.5, pp.86–87; B.5.1, pp.99–103;
F.9.18(7), pp.325–326; proof of 13.8.20, printed p.955 (PDF p.972),
combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.SL3FourNaturalDual
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual central quotient of [V,K], with one common group marking on
all natural copies. This is an output to construct, never an intrinsic input. -/
structure RepeatedNaturalSection (ρ : Representation (ZMod 2) D V) (K : Subgroup D) where
  sectionData : MovedSection ρ K
  marking : K ≃* SL
  copies : ℕ
  positive : 0 < copies
  coordinates : (sectionData.space.toSubmodule ⧸ sectionData.central.toSubmodule) ≃ₗ[ZMod 2]
    (Fin copies → W)
  natural_action : ∀ (g : K) (w : sectionData.space.toSubmodule ⧸ sectionData.central.toSubmodule)
    (i : Fin copies), coordinates (MovedSection.action ρ sectionData (g : D) w) i =
      natural (marking g) (coordinates w i)

/-- The precise universal change-of-marking implication; its separate model
owner proves it without making assumptions about the representation. -/
def GraphRemarking : Prop :=
  ∀ (β : MulAut SL) (c : Matrix.GeneralLinearGroup (Fin 3) F),
    ∃ c' : Matrix.GeneralLinearGroup (Fin 3) F, ∀ g,
      β (Matrix.PSL3.OuterSolvable.linearConjSL F c
        (Matrix.SpecialLinearGroup.inverseTranspose (β.symm g))) =
      Matrix.PSL3.OuterSolvable.linearConjSL F c'
        (Matrix.SpecialLinearGroup.inverseTranspose g)

/-- The obstruction holds on the literal moved central section, with its
induced D-action and its actual marking. -/
theorem RepeatedNaturalSection.false_of_graph
    {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    (s : RepeatedNaturalSection ρ K) (t : D)
    (c : Matrix.GeneralLinearGroup (Fin 3) F)
    (ht : ∀ g, (s.marking.symm g : D) * t = t * (s.marking.symm
      (Matrix.PSL3.OuterSolvable.linearConjSL F c
        (Matrix.SpecialLinearGroup.inverseTranspose g)) : D)) : False := by
  let : Nonempty (Fin s.copies) := ⟨⟨0, s.positive⟩⟩
  apply no_graph_extension_of_repeated_natural (MovedSection.action ρ s.sectionData)
    (K.subtype.comp s.marking.symm.toMonoidHom) t s.coordinates c
  · intro g w i
    simpa using s.natural_action (s.marking.symm g) w i
  · exact ht

/-- Recognition may change the marking of K. The original graph relation
still contradicts the recognized section, conditional only on the universal
model remarking implication and the explicitly supplied section witness. -/
theorem RepeatedNaturalSection.false_of_remarking
    {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    (s : RepeatedNaturalSection ρ K) (remark : GraphRemarking)
    (e : K ≃* SL) (t : D) (c : Matrix.GeneralLinearGroup (Fin 3) F)
    (ht : ∀ g, (e.symm g : D) * t = t * (e.symm
      (Matrix.PSL3.OuterSolvable.linearConjSL F c
        (Matrix.SpecialLinearGroup.inverseTranspose g)) : D)) : False := by
  let β : MulAut SL := e.symm.trans s.marking
  obtain ⟨c', hc'⟩ := remark β c
  apply s.false_of_graph t c'
  intro g
  have h := ht (β.symm g)
  have hleft : e.symm (β.symm g) = s.marking.symm g := by simp [β]
  have hright : e.symm (Matrix.PSL3.OuterSolvable.linearConjSL F c
        (Matrix.SpecialLinearGroup.inverseTranspose (β.symm g))) =
      s.marking.symm (Matrix.PSL3.OuterSolvable.linearConjSL F c'
        (Matrix.SpecialLinearGroup.inverseTranspose g)) := by
    apply s.marking.injective
    simpa only [β, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using hc' g
  simpa only [hleft, hright] using h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF

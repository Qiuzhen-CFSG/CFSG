module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.SymplecticFour.Interfaces

/-!
# Assembly of the symplectic field-component fixer calculation

The genuine projective-to-matrix equivalence transports the given involution.
The cyclic outer quotient reduces it to an inner involution or a field twist;
the inner case is excluded and symplectic cocycle descent supplies a compatible
conjugator in the other case. Subnormality then identifies the actual component
with the embedded derived subfield group. Rigidity of its full automorphism fixer
gives order exactly two and transports back through the same ambient equivalence.

The shared coverage and descent inputs, inner exclusion, and explicit fixer
rigidity remain proof obligations. This is a conditional assembly, not an
unconditional proof of `ComponentFixerBound`. No binary endpoint is discarded:
the embedded subgroup at n = 1 is Sp₄(2)′, identified with A₆ by the polar map.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.4(4),
16.1.7(3a), and 16.3.5, printed pp.1171–1173 and 1178–1179.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
open CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical.SymplecticFour
universe u

/-- The four explicit model inputs yield the full intrinsic bound, uniformly
in the universe of the ambient simple group. -/
theorem componentFixerBound_of_inputs
    (hcover : DiagramCoverage) (hdescent : FieldCocycleDescent)
    (hinner : InnerComponentExclusion.{u}) (hfix : ResidualFixerRigidity) :
    ComponentFixerBound.{u} FieldFamily.symplecticFour := by
  intro S hS hfin hsimple hperfect n hn hmodel a ha P hP hZ hsmall
  obtain ⟨F, hF, hFfin, hcard, ⟨e₀⟩⟩ := hmodel
  let := EvenProjective.charTwo_of_card hcard
  let e : S ≃* Sp F := e₀.trans EvenProjective.equiv.symm
  let b := MulAut.congr e a
  have hb : orderOf b = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective a).trans ha
  have heb (x : S) : e (a x) = b (e x) := by
    change e (a x) = e (a (e.symm (e x)))
    rw [e.symm_apply_apply]
  rcases involution_inner_or_twist hcard (by omega) (hcover F) b hb with
    ⟨g, hg, hbg⟩ | ⟨g, hbg, hg⟩
  · have hia : a = MulAut.conj (e.symm g) := by
      apply MulEquiv.ext
      intro x
      apply e.injective
      rw [heb, hbg]
      simp only [MulAut.conj_apply, map_mul, map_inv, e.apply_symm_apply]
    have horder : orderOf (e.symm g) = 2 :=
      (orderOf_injective e.symm.toMonoidHom e.symm.injective g).trans hg
    exact (hinner S n hn ⟨F, hF, hFfin, hcard, ⟨e₀⟩⟩ (e.symm g) horder P
      (hia ▸ hP) hZ hsmall).elim
  · have hgraph : ExceptionalGraph.graphAut (F := F) ^ (2 * n) = representative n := by
      simpa using graph_pow_eq_field_of_even (even_two_mul n)
    rw [hgraph] at hbg hg
    obtain ⟨h, hh⟩ := hdescent F n hn hcard g hg
    have heq : b = MulAut.conj h * representative n * (MulAut.conj h)⁻¹ :=
      hbg.trans (inner_twist_eq_conjugate _ g h hh)
    let d : S ≃* Sp F := e.trans (MulAut.conj h).symm
    have hd (x : S) : d (a x) = representative n (d x) := by
      change (MulAut.conj h).symm (e (a x)) = representative n ((MulAut.conj h).symm (e x))
      rw [heb, heq]
      exact (MulAut.conj h).symm_apply_apply _
    have hmap := FieldComponent.component_map_eq_embedded_of_compatible hn hcard d a hd P hP
    have hc := FieldComponent.card_fixer_eq_two_of_le_zpowers hn hcard (hfix F n hn hcard)
    rw [← MulAut.card_fixingSubgroup_map d P, hmap, hc]
    decide

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical.SymplecticFour

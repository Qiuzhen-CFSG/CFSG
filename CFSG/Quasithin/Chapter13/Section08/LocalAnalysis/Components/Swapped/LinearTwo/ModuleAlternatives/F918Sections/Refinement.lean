module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement.Geometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement.Models

/-!
# The intrinsic general-exponent refinement of F.9.18(5)

Starting from the complete five-case conclusion, an actual PSL₂(F)
identification excludes each L₃(2) tensor or multiplicity case by the
checked two-rank/order comparison. The natural constituent list excludes
Suzuki by order divisibility; it retains A₅ exactly at n = 2 and the
Hermitian constituent at n = 2m. Equality of the defining-field exponents
is proved using actual group equivalences, with no oddness assumption.

In the factor case the literal canonical commutator spaces sum to the
module and centralize the opposite factors. Their central quotients carry
compatible intertwining identifications. In the orthogonal case the full
orbit span is the actual natural module, with no further quotient.

The inputs are a finite faithful binary action of the generated actor,
a normal marked product of quasisimple components, an actual moving
element, the homogeneous Irr⁺ section, its full ambient orbit, and the
unfiltered earlier F.9.18(5) conclusion. The parent supplies that earlier
source theorem and constructs the section and orbit identity; in the
literal source action, source_moved_eq_top/source_section_eq_top give
the required full Ũ_H. Neither the no-strong argument nor the independent
orthogonal contradiction is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.18(5),
printed pp.325–326, and 13.8.16(1b1,b2), p.952 (PDF p.969).
-/

open Subgroup Representation Representation.BinaryOffender Matrix
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
open SourceRestrictions SourceRestrictions.Cases SourceRestrictions.Cases.Exchanged
open PairCoordinates
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement
@[expose] public noncomputable section
attribute [local instance] Exchanged.fixedBinaryAlgebra Exchanged.hermitianBinaryModule
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {K K₀ T : Subgroup D}
  {I : Submodule (ZMod 2) V}
  {F : Type} [Field F] [Finite F] {n : ℕ}

private theorem alternatingFive_exponent (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : PSL(2,F) ≃* alternatingGroup (Fin 5)) : n = 2 := by
  have hc := congrArg (fun c : ℕ => c.factorization 2) (Nat.card_congr e.toEquiv)
  rw [(FFExclusions.ModelRigidity.pslTwo_invariants hn hF).2] at hc
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rw [hA] at hc
  exact hc.trans (by decide +kernel)

theorem factorModules_of_constituent {t : D} (p : ProductMarking K K₀ t)
    {hI : K₀ ≤ subspaceStabilizer ρ I}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(2,F))
    (hcross : subspaceCommutator ρ I (K.conjBy t⁻¹) = ⊥)
    (hfirst : subspaceCommutator ρ ⊤ K = I)
    (h : FiveNatural ρ K K₀ p.le I hI ∨ FiveEvenOrthogonal ρ K K₀ p.le I hI) :
    FactorModules ρ K t n := by
  rcases h with h | ⟨m, hm, ⟨d⟩⟩
  · cases h with
    | linear E m hm hE d =>
      have he := pslTwo_exponent_eq hn hm hF hE
        (e.symm.trans (d.groupEquiv.trans sl2ProjectiveEquiv))
      exact .natural E (he ▸ hE) (pairedIdentification ρ p hcross hfirst d)
    | suzuki m hm d =>
      exact (pslTwo_not_suzuki (F := F) m hm ⟨e.symm.trans d.groupEquiv⟩).elim
    | alternatingFive d =>
      exact .alternatingFive (alternatingFive_exponent hn hF (e.symm.trans d.groupEquiv))
        (pairedIdentification ρ p hcross hfirst d)
    | binaryThree d =>
      exact (pslTwo_not_binaryThree hn hF ⟨e.symm.trans
        (d.groupEquiv.trans (sl3ProjectiveEquiv (f := 1) (by simp) (by decide)))⟩).elim
  · let := hm
    have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have hE : Nat.card (OrthogonalFourMinus.FiniteModel.Field m) = 2 ^ (2*m) :=
      GaloisField.card 2 (2*m) (Nat.mul_ne_zero (by decide) (NeZero.ne m))
    have he := pslTwo_exponent_eq hn (by omega) hF hE
      (e.symm.trans (d.groupEquiv.trans sl2ProjectiveEquiv))
    exact .evenOrthogonal m he (pairedIdentification ρ p hcross hfirst d)

/-- Complete intrinsic refinement; the input remains the unfiltered five-case output. -/
theorem of_full_five [Finite D] [Finite V] [K₀.Normal]
    [Theory.GroupTheory.IsQuasisimple K]
    {t : D} (p : ProductMarking K K₀ t) (_ht : t ∈ T)
    (_hmoving : t ∉ normalizer (K : Set D))
    (_faithful : Function.Injective ρ)
    (hi : IsIrrPlusWith ρ K₀ T I) (hgen : K₀ ⊔ T = ⊤)
    (hfull : orbitSpan ρ ⊤ I = ⊤)
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(2,F))
    (full : FullFiveConclusion ρ K K₀ T p.le I hi.invariant) :
    Conclusion ρ K K₀ t n := by
  have hnpos : 0 < n := by omega
  have hN := Marking.normalizes_first p
  cases full.alternatives with
  | orthogonal E m hm hE a hinv d =>
    have he := pslTwo_exponent_eq hnpos hm hF hE (e.symm.trans a)
    exact .orthogonal E (he ▸ hE) (orthogonalIdentification_of_literal ρ hinv hfull d)
  | tensor a _ _ =>
    exact (pslTwo_not_binaryThree hnpos hF ⟨e.symm.trans a⟩).elim
  | constituent s split first hm =>
    obtain ⟨ps⟩ := Marking.remark p split.outside
    obtain ⟨hfirst, hsecond, hsum, hcross₁, hcross₂⟩ :=
      canonical_spaces ρ ps hi hgen hfull hN split first
    have hsi : s⁻¹ ∉ normalizer (K : Set D) :=
      fun h => split.outside (by simpa using (normalizer _).inv_mem h)
    have he : K.conjBy s⁻¹ = K.conjBy t⁻¹ := Marking.conjugate_eq p hsi
    have hc : subspaceCommutator ρ I (K.conjBy t⁻¹) = ⊥ := by
      apply (subspaceCommutator_eq_bot_iff ρ I _).mpr
      rw [← hfirst, ← he]
      exact hcross₁
    refine .factors ⟨he ▸ hsum, right_conjugate_moved ρ t, he ▸ hcross₁, he ▸ hcross₂, ?_,
      factorModules_of_constituent ρ p hnpos hF e hc hfirst hm⟩
    have hd := split.disjoint
    rw [hfull, right_conjugate_moved ρ s, he] at hd
    exact hd
  | twoBinaryThree _ _ _ a _ _ _ _ _ _ =>
    exact (pslTwo_not_binaryThree hnpos hF ⟨e.symm.trans a⟩).elim
  | fourBinaryThree _ _ a _ _ _ =>
    exact (pslTwo_not_binaryThree hnpos hF ⟨e.symm.trans a⟩).elim

end
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement

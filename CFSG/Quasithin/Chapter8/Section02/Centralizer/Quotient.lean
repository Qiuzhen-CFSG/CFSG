module

public import Theory.Representation.Mathieu.M22James.Ambient
public import Theory.Representation.Mathieu.M22James.Classification
public import CFSG.Quasithin.Chapter8.Section02.NormalClosure

/-!
# Recognizing the covering extension on the centralizer quotient

James's module equivalence places a faithful action extending the irreducible
twelve-dimensional triple-cover module in its actual matrix normalizer.
A proper extension has the full matrix image because the cover has index two.
The resulting isomorphism retains the normal cubic subgroup: conjugation on
M₂₂ has exactly this kernel and is onto Aut(M₂₂).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 8.2.13,
printed pp.722–723, using H.12.1. The component, properness, and faithful
irreducible action are explicit premises, still to be constructed from the
source setup. These deductions do not assert the full proposition.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter8.Section02.Centralizer
open Subgroup Sporadic.Mathieu
open Sporadic.Mathieu.M22TripleCover.Ambient
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension

noncomputable section

/-- A faithful binary action extending the twelve-dimensional irreducible
triple-cover module identifies every proper ambient extension with the actual
matrix group 3.M₂₂.2. The scalar kernel survives this equivalence. -/
def coveringExtensionEquiv {Q W : Type*} [Group Q]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Q W) (hf : Function.Injective ρ)
    (K : Subgroup Q) [K.Normal] (e : K ≃* M22TripleCover)
    [Representation.IsIrreducible (ρ.comp K.subtype)]
    (hd : Module.finrank (ZMod 2) W = 12) (hproper : K ≠ ⊤) :
    Q ≃* actionGroup := by
  let E := Classical.choice (M22TripleCover.equiv_representationOfEquiv_of_finrank_twelve
    e (ρ.comp K.subtype) (hf.comp K.subtype_injective) hd)
  let f := markedTripleAmbientHom ρ K e E
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rcases markedTripleAmbientHom_range_cases ρ K e E with h | h
    · exfalso
      apply hproper
      apply top_unique
      intro g _
      apply (markedTripleAmbientHom_mem_cover_iff ρ K e E hf g).mp
      rw [← h]
      exact ⟨g, rfl⟩
    · exact h
  exact MulEquiv.ofBijective f ⟨markedTripleAmbientHom_injective ρ K e E hf, hsurj⟩

/-- Every group identified with the actual extension has a normal cubic
kernel and automorphism-group quotient. It is not identified with that quotient. -/
theorem exists_cubic_kernel_of_coveringExtension {Q : Type*} [Group Q]
    (e : Q ≃* actionGroup) :
    ∃ π : Q →* MulAut M22, Function.Surjective π ∧ Nat.card π.ker = 3 := by
  let π := quotientConjugation.comp e.toMonoidHom
  refine ⟨π, quotientConjugation_surjective.comp e.surjective, ?_⟩
  have hmap : π.ker.map e.toMonoidHom = scalarSubgroup := by
    change (quotientConjugation.ker.comap e.toMonoidHom).map e.toMonoidHom = _
    rw [map_comap_eq_self_of_surjective e.surjective,
      quotientConjugation_ker]
  rw [← card_map_of_injective (K := π.ker) (f := e.toMonoidHom) e.injective, hmap, scalarSubgroup_card]

/-- The quotient step of 8.2.13 on the literal centralizer quotient. The
component classification, its properness, and the faithful irreducible action
are still source obligations; no group-shape conclusion is assumed. -/
theorem centralizerQuotient_coveringExtension {G : Type*} [Group G]
    (z : G) (Vz : Subgroup (centralizer ({z} : Set G)))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2)
      ((centralizer ({z} : Set G)) ⧸ centralizerClosure z Vz) W)
    (hf : Function.Injective ρ)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ centralizerClosure z Vz))
    [K.Normal] (e : K ≃* M22TripleCover) [Representation.IsIrreducible (ρ.comp K.subtype)]
    (hd : Module.finrank (ZMod 2) W = 12) (hproper : K ≠ ⊤) :
    Nonempty (((centralizer ({z} : Set G)) ⧸ centralizerClosure z Vz) ≃* actionGroup) ∧
      ∃ π : ((centralizer ({z} : Set G)) ⧸ centralizerClosure z Vz) →* MulAut M22,
        Function.Surjective π ∧ Nat.card π.ker = 3 := by
  let f := coveringExtensionEquiv ρ hf K e hd hproper
  exact ⟨⟨f⟩, exists_cubic_kernel_of_coveringExtension f⟩

end
end CFSG.Quasithin.Chapter8.Section02.Centralizer

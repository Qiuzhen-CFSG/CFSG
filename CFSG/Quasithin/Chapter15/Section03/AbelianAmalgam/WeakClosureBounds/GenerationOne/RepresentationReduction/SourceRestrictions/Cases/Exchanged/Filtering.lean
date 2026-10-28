module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.SourceAlternatives

/-!
# Filtering F.9.18(5) against the actual E.2.2 exchanged model

Exceptional groups are excluded by concrete group invariants. The even
orthogonal constituent is excluded only after recovering its defining field
from the source component. In the natural branch the equality of hatted
IK and I transports through right conjugation; full commutator generation
then gives the literal T-orbit and cross-centralization statements.

Source: Aschbacher--Smith, F.9.18(5), pp.325--326, E.2.2, pp.215--216,
and the deduction of (i),(iii) on printed p.1152.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open RemainingModels BorelReduction BorelReduction.SourceCases

attribute [local instance] fixedBinaryAlgebra hermitianBinaryModule

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {K K₀ T : Subgroup D}
    {hK : K ≤ K₀} {I : Submodule (ZMod 2) V} {hI : K₀ ≤ subspaceStabilizer ρ I}

/-- The two natural rows after the model and defining-field comparisons. -/
inductive FilteredNatural (f : ℕ) : Prop
  | linear (F : Type) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
      (card : Nat.card F = 2 ^ f)
      (identification : HatIdentification ρ K K₀ hK I hI
        (restrictScalars (specialLinearNatural (k := F) 2)))
  | suzuki (m : ℕ) (positive : 0 < m) (exponent : f = 2 * m + 1)
      (identification : HatIdentification ρ K K₀ hK I hI (suzukiNatural m))

variable {G : Type*} [Group G] {H M L : Subgroup G} {f : ℕ}
  (source : ExchangedModel H M L f) (comparison : K ≃* sourceImage H M L)

include source comparison

/-- The full natural list is filtered using actual group equivalences. -/
theorem FiveNatural.filter (hf : 1 < f) (ho : Odd f)
    (h : FiveNatural ρ K K₀ hK I hI) :
    FilteredNatural ρ (hK := hK) (hI := hI) f := by
  cases h with
  | linear F n hn hF d =>
    exact .linear F (source_linear_field_card source hn hF
      (comparison.symm.trans (d.groupEquiv.trans sl2ProjectiveEquiv))) d
  | suzuki m hm d =>
    exact .suzuki m hm
      (source_suzuki_exponent source hm (comparison.symm.trans d.groupEquiv)) d
  | alternatingFive d =>
    exact (source_not_alternatingFive source hf ho ⟨comparison.symm.trans d.groupEquiv⟩).elim
  | binaryThree d =>
    exact (source_not_binaryThree source ⟨comparison.symm.trans
      (d.groupEquiv.trans (sl3ProjectiveEquiv (f := 1) (by simp) (by decide)))⟩).elim

/-- The discarded orthogonal row has field order 2^(2n); identify that
field with the source exponent before using oddness. -/
theorem FiveEvenOrthogonal.excluded (ho : Odd f)
    (h : FiveEvenOrthogonal ρ K K₀ hK I hI) : False := by
  obtain ⟨n, hn, ⟨d⟩⟩ := h
  let := hn
  have hcard : Nat.card (OrthogonalFourMinus.FiniteModel.Field n) = 2 ^ (2 * n) :=
    GaloisField.card 2 (2 * n) (Nat.mul_ne_zero (by decide) (NeZero.ne n))
  exact source_not_even_orthogonal source ho (Nat.pos_of_ne_zero (NeZero.ne n)) hcard
    ⟨comparison.symm.trans (d.groupEquiv.trans sl2ProjectiveEquiv)⟩

omit source comparison in
/-- (5iiia)'s hatted first-constituent identity suffices for all literal
orbit conclusions. The proof normalizes K₀, never the individual K by T. -/
theorem FiveSplit.literal {t : D} (s : FiveSplit ρ K K₀ T I t)
    (hi : IsIrrPlusWith ρ K₀ T I) (hN : K₀ ≤ normalizer (K : Set D))
    (first : (subspaceCommutator ρ (orbitSpan ρ ⊤ I) K).map (fixedSpace ρ K₀).mkQ =
      I.map (fixedSpace ρ K₀).mkQ) :
    orbitSpan ρ T I = I ⊔ rightConjugate ρ I t ∧
      subspaceCommutator ρ I (K.conjBy t⁻¹) = ⊥ := by
  have ht := hi.normalizes (T.inv_mem s.mem_T)
  have hsecond :
      (rightConjugate ρ (subspaceCommutator ρ (orbitSpan ρ ⊤ I) K) t).map
        (fixedSpace ρ K₀).mkQ =
      (rightConjugate ρ I t).map (fixedSpace ρ K₀).mkQ := by
    unfold rightConjugate
    rw [quotientImage_map_normalizer ρ K₀ _ ⟨t⁻¹, ht⟩,
      quotientImage_map_normalizer ρ K₀ _ ⟨t⁻¹, ht⟩, first]
  have hpair : (orbitSpan ρ ⊤ I).map (fixedSpace ρ K₀).mkQ =
      (I ⊔ rightConjugate ρ I t).map (fixedSpace ρ K₀).mkQ := by
    rw [Submodule.map_sup, s.sum, first, hsecond]
  exact ⟨orbitSpan_eq_pair_of_ambient_image ρ hi le_top s.mem_T hpair,
    cross_commutator_eq_bot_of_source_images ρ hi.isIrrPlus le_top hN t
      first.symm.le s.centralizer⟩

/-- The surviving cases retain the source data as well as the newly proved
literal identities; they do not replace the complete earlier input. -/
inductive FilteredFive (f : ℕ) : Prop
  | orthogonal (F : Type) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
      (card : Nat.card F = 2 ^ f)
      (invariant : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ I)
      (identification : LiteralIdentification ρ K₀ I hI (omegaNatural (F := F)))
  | natural (t : D) (mem_T : t ∈ T) (outside : t ∉ normalizer (K : Set D))
      (orbit : orbitSpan ρ T I = I ⊔ rightConjugate ρ I t)
      (cross : subspaceCommutator ρ I (K.conjBy t⁻¹) = ⊥)
      (natural : FilteredNatural ρ (hK := hK) (hI := hI) f)

/-- Exhaustive filtering of all five source rows. All three L₃(2) rows,
the A₅ constituent and the even-field constituent are explicitly eliminated. -/
theorem FullFiveConclusion.filter (hf : 1 < f) (ho : Odd f)
    (hi : IsIrrPlusWith ρ K₀ T I) (hN : K₀ ≤ normalizer (K : Set D))
    (h : FullFiveConclusion ρ K K₀ T hK I hI) :
    FilteredFive ρ (T := T) (hK := hK) (hI := hI) f := by
  cases h.alternatives with
  | orthogonal F n hn hF a hinv d =>
    exact .orthogonal F (source_linear_field_card source hn hF (comparison.symm.trans a)) hinv d
  | tensor a _ _ =>
    exact (source_not_binaryThree source ⟨comparison.symm.trans a⟩).elim
  | constituent t split first hm =>
    rcases hm with hm | hm
    · obtain ⟨horbit, hcross⟩ := split.literal ρ hi hN first
      exact .natural t split.mem_T split.outside horbit hcross
        (hm.filter ρ source comparison hf ho)
    · exact (hm.excluded ρ source comparison ho).elim
  | twoBinaryThree _ _ _ a _ _ _ _ _ _ =>
    exact (source_not_binaryThree source ⟨comparison.symm.trans a⟩).elim
  | fourBinaryThree _ _ a _ _ _ =>
    exact (source_not_binaryThree source ⟨comparison.symm.trans a⟩).elim

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged

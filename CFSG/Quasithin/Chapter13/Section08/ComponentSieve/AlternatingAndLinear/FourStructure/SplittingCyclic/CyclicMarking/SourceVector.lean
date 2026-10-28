module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.RadicalPlacement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicAction

/-!
# The actual marked V₂ vector in the central section

The kernel of the specified quotient is V₁. Consequently |V₂:V₁| = 2
makes its image a binary line, and normalization by T makes that line
pointwise fixed by T*. Since V₂ lies in V₃, the generating irreducible
seed forces every nonzero image vector outside every proper H-submodule.
All images use the same conjugation section and the actual source subgroups.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Notation 13.2.1, recalled on printed p.916,
and 13.8.25, printed pp.961–962 (PDF pp.978–979). Membership of this vector
in [Ũ_H,Uα*] requires an additional action argument and is not asserted here.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking
open Subgroup Representation Representation.BinaryOffender
open CriticalTransfer CriticalTransfer.MarkedGeometry

variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  {H UH Z V₃ V₁ : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- The source index is computed using the actual quotient kernel. -/
theorem image_finrank_one (s : ConjugationSection H UH Z ρ)
    (V₂ : Subgroup G) (hV₂ : V₂ ≤ UH) (hidx : Z.relIndex V₂ = 2) :
    Module.finrank (ZMod 2) (s.image V₂) = 1 := by
  have hz : (Z.subgroupOf UH).map s.quotient = ⊥ := by
    rw [← s.kernel]
    exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
  have hc := s.relativeIndex_image V₂ Z hV₂ le_rfl
  rw [hz, Subgroup.relIndex_bot_left, hidx] at hc
  have hc' : Nat.card (s.image V₂) = 2 := hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc'
  have hh := congrArg (Nat.log 2) hc'
  simpa only [Nat.log_pow (by decide : 1 < 2), show Nat.log 2 2 = 1 by decide] using hh

omit [FiniteDimensional (ZMod 2) U] in
/-- Ambient normalization transports to the specified image and source quotient actor. -/
theorem image_stable_of_normalizes (s : ConjugationSection H UH Z ρ)
    (X T : Subgroup G) (hT : T ≤ normalizer (X : Set G)) :
    Source.starImage H T ≤ subspaceStabilizer ρ (s.image X) := by
  apply le_subspaceStabilizer
  rintro _ ⟨t, ht, rfl⟩ v hv
  obtain ⟨u, hu, rfl⟩ := (s.mem_image X v).mp hv
  rw [s.conjugates]
  exact ⟨_, (mem_normalizer_iff.mp (hT ht) u).mp hu, rfl⟩

/-- T-invariance of V₂ fixes its entire one-dimensional image, not just its head image. -/
theorem image_line_fixed (s : ConjugationSection H UH Z ρ)
    (V₂ T : Subgroup G) (hV₂ : V₂ ≤ UH) (hidx : Z.relIndex V₂ = 2)
    (hT : T ≤ normalizer (V₂ : Set G)) :
    s.image V₂ ≤ fixedSpace ρ (Source.starImage H T) :=
  binary_line_fixed_of_stable ρ _ (image_finrank_one s V₂ hV₂ hidx) _
    (image_stable_of_normalizes s V₂ T hT)

/-- A nonzero vector in the actual V₂ image is fixed by T* and lies outside every proper W.
No commutator-space membership is assumed or claimed by this preliminary construction. -/
theorem exists_source_fixed_vector
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (V₂ L₁ T : Subgroup G) (h₂₃ : V₂ ≤ V₃) (hidx : V₁.relIndex V₂ = 2)
    (hTV₂ : T ≤ normalizer (V₂ : Set G)) (hT : IsPGroup 2 T)
    (hstable : ∀ a : Source.starImage H (L₁ ⊔ T), ∀ v ∈ s.image V₃,
      ρ a v ∈ s.image V₃)
    (hirr : IsAtom (⟨s.image V₃, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ T)).subtype)))
    (hdim : Module.finrank (ZMod 2) (s.image V₃) = 2)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) :
    ∃ v : U, v ∈ s.image V₂ ∧ v ≠ 0 ∧
      v ∈ fixedSpace ρ (Source.starImage H T) ∧ v ∉ W.toSubmodule := by
  let seed := sourceGeneratingSeed s L₁ T hT hstable hirr hdim
  have hV₂U := h₂₃.trans (le_conjugateSpanBy V₃ H)
  have hline := image_finrank_one s V₂ hV₂U hidx
  have hne : s.image V₂ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hline
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv, hv0, image_line_fixed s V₂ T hV₂U hidx hTV₂ hv, ?_⟩
  intro hvW
  exact hv0 ((Submodule.disjoint_def.mp (seed.disjoint_proper ρ W hW)) v
    (s.image_mono h₂₃ hv) hvW)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking

module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.Structure
public import Theory.Representation.BinaryOffender.FixedSpaceCentralizerDichotomy

/-!
# Constructing the strict pointwise-centralizer conclusion

For the original critical actors, Uγ* ≤ Vγ* follows from V₃ ≤ V, and the
13.8.18 rank bound makes this containment strict. The intrinsic A₇ quotient
and H = KT supply the monolith; the rank-one bound on Uγ* then proves fixed
vector lifting on the actual submodule and quotient of U_H/V₁. The image of
A₁ has dimension at most one because |V₁| = 2. The fixed-space displacement
bound therefore forces Vγ* into one of the two pointwise centralizers.

This constructs the conclusion used as `Earlier.strict_centralizer` and
applies it to the terminal seven-point contradiction. The geometric bound
on the ambient fixed space is still explicit: it must be obtained from the
literal centralizer identification and 13.7.3(7) in source assembly. Neither
this bound nor the compatible natural embeddings is claimed here outright.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.23–24, printed pp.958–959.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open TransvectionRecognition.Component.ModelExtension CriticalGeometry PairsBranch

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hKn : (K.subgroupOf H).Normal) (hKT : K ⊔ (T : Subgroup G) = H)
  (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (W : Subrepresentation ρ) (c : CriticalPair L (T : Subgroup G) H V)
  (hKW : ∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w)
  (hKQ : ∃ k ∈ Source.starImage H K,
    ∃ q : Additive (Source.Utilde H V₃ V₁) ⧸ W.toSubmodule,
      W.quotientRepresentation k q ≠ q)
  (hA : (Source.starImage H (c.Ugamma V₃)) ≠ ⊥)
  (hrank : rank (Source.starImage H (c.Ugamma V₃)) = 1)
  (hbound : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤
    2 * rank (Source.starImage H (c.Ugamma V₃)))
  (hVrank : 1 < rank (Source.starImage H c.Vgamma))
  (hdisp : ∀ b ∈ Source.starImage H c.Vgamma,
    ∀ v ∈ fixedSpace ρ (Source.starImage H (c.Ugamma V₃)),
      ρ b v - v ∈ sourceImage H V₃ V₁ (c.Aone V₁))

include d hH hKH hK hKn hKT e hKW hKQ hA hrank hbound hVrank hdisp

/-- Construct the exact strict-centralizer clause on the original two
sections from the critical-line displacement estimate. -/
theorem source_strict_centralizer :
    Source.starImage H (c.Ugamma V₃) <
      subspaceKernel W.toRepresentation
        (fixedSpace W.toRepresentation (Source.starImage H (c.Ugamma V₃))) ⊤ ∨
    Source.starImage H (c.Ugamma V₃) <
      subspaceKernel W.quotientRepresentation
        (fixedSpace W.quotientRepresentation (Source.starImage H (c.Ugamma V₃))) ⊤ := by
  have hUV : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono d.seed_le le_rfl)
  have hlt : Source.starImage H (c.Ugamma V₃) < Source.starImage H c.Vgamma := by
    apply lt_of_le_of_ne (LocalGeometry.starImage_mono H hUV)
    intro he
    rw [← he, hrank] at hVrank
    omega
  have hcard : Nat.card (c.Aone V₁) = 2 := by
    rw [show c.Aone V₁ = V₁.map (MulAut.conj (c.gb : G)).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj (c.gb : G)).injective, d.line_card]
  have hdim : Module.finrank (ZMod 2) (sourceImage H V₃ V₁ (c.Aone V₁)) ≤ 1 := by
    simpa only [hcard, show Nat.log 2 2 = 1 from by decide] using
      SourceExclusion.source_image_rank_le (H := H) (V₃ := V₃) (V₁ := V₁) (c.Aone V₁)
  have hlift := (source_rank_one_sections hH hKH hK hKn hKT e ρ W
    (Source.starImage H (c.Ugamma V₃)) hKW hKQ hA hrank hbound).2.2.2.2.2
  rcases fixedSpace_kernel_dichotomy ρ W (Source.starImage H (c.Ugamma V₃))
      (Source.starImage H c.Vgamma) (sourceImage H V₃ V₁ (c.Aone V₁)) hdim hlift hdisp with hw | hq
  · exact Or.inl (hlt.trans_le hw)
  · exact Or.inr (hlt.trans_le hq)

/-- The actual terminal application now derives the strict-centralizer input.
The independent representation producer still supplies both natural embeddings. -/
theorem source_no_rank_one_configuration
    (φ : Source.Hstar H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (helem : IsElementaryAbelian 2 (Source.starImage H (c.Ugamma V₃)))
    (hW : HasNaturalSubmodule W.toRepresentation φ)
    (hQ : HasNaturalSubmodule W.quotientRepresentation φ) : False := by
  exact no_rank_one_critical_configuration ρ φ hφ W (Source.starImage H K)
    (Source.starImage H (c.Ugamma V₃)) (source_structure hH hKH hK hKn hKT e).2.2
    hKW hKQ ⟨hA, helem⟩ hrank hbound hW hQ
    (source_strict_centralizer d hH hKH hK hKn hKT e ρ W c hKW hKQ hA hrank hbound hVrank hdisp)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource

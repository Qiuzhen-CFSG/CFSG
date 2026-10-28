module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData.Indices
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData.Modules

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData.Eligibility

/-!
# The eligible reversed source pair for the L₄ equality case

`exists_eligible_reversal` constructs the genuine reversed critical geodesic,
including its neighbor and both edge-stabilizer adjustments. Equality exchanges
the actual denominator codimension and actor rank, so the reversed pair is
numerically eligible. `Eligibility` then proves its own elementary quadratic
action, both nonsplitting exclusions, actual marked radical placement and
A₁ ≰ I, retaining the same central section and natural-module coordinates.
`Reversal.endpoint_modules` records the compatible unnormalized endpoint data.

Only the earlier F.9 geometry/core and 13.8.18(1) generation are supplied
uniformly. The intrinsic source and chief-factor data, including the precise
two-factor B.4.9(1) premise, are explicit in `SourceData`. No fixed-pair marked
or nonsplitting hypothesis is silently generalized. The parent can apply the
proved `Eligible.forward` to the returned pair, and `Reversal.line_containment`
identifies that conclusion with A₁ ≰ U_H. The final fixation and 13.8.25
contradiction remain in the parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Remark F.9.17,
printed p.324, and the equality case of 13.8.25, printed p.962.
-/

public section

open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  {L T H V : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- Identify the endpoint subgroup using the actual normalized edge transporter. -/
theorem Reversal.endpoint_image {c : CriticalPair L T H V} (r : Reversal c)
    (Q : Subgroup G) (hQ : H ≤ normalizer (Q : Set G)) :
    Q.map (MulAut.conj (r.pair.gb : G)).toMonoidHom =
      (Q.map (MulAut.conj (c.gb : G)⁻¹).toMonoidHom).map
        (MulAut.conj (r.adjustment : G)⁻¹).toMonoidHom := by
  rw [r.conjugator_val]
  exact adjusted_conjugate H Q _ _ _ hQ

/-- Once the universal forward implication is applicable to the constructed
pair, its line noncontainment is exactly the parent's desired noncontainment. -/
theorem Reversal.line_containment {c : CriticalPair L T H V} (r : Reversal c)
    (V₃ V₁ : Subgroup G) (s : ConjugationSection H (Source.UH H V₃) V₁ ρ) :
    V₁ ≤ r.pair.Ugamma V₃ ↔ c.Aone V₁ ≤ Source.UH H V₃ := by
  change V₁ ≤ (Source.UH H V₃).map (MulAut.conj (r.pair.gb : G)).toMonoidHom ↔ _
  rw [r.conjugator_val]
  exact adjusted_line_containment H _ _ _ _ _ s.normalizes
    (s.centralizes.trans (centralizer_le_normalizer _))

/-- Equality makes the constructed reversed graph pair numerically eligible.
Actor-specific marked and nonsplitting eligibility is not a conclusion here. -/
theorem exists_numerically_eligible_reversal [FiniteDimensional (ZMod 2) U]
    (V₃ V₁ : Subgroup G) (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hfaith : Function.Injective ρ) (hb : 3 ≤ c.path.length)
    (hUV : c.Ugamma V₃ ≤ c.Vgamma) (hVH : c.Vgamma ≤ H)
    (hF915 : c.Vgamma ⊓ firstKernel L T H (base L T H true) =
      Source.Egamma c.Vgamma (Source.UH H V₃) V₁)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hrank : 1 < rank (Source.starImage H (c.Ugamma V₃)))
    (hequal : Module.finrank (ZMod 2)
      (U ⧸ s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))) =
      rank (Source.starImage H (c.Ugamma V₃))) :
    ∃ r : Reversal c,
      1 < rank (Source.starImage H (r.pair.Ugamma V₃)) ∧
      Module.finrank (ZMod 2)
        (U ⧸ s.image (Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone V₁))) =
        rank (Source.starImage H (r.pair.Ugamma V₃)) := by
  obtain ⟨r⟩ := exists_reversal_of_rank V₃ V₁ c s hfaith hb hUV hVH hF915 (by omega)
  have hh := adjusted_equality_numerical_choice s (c.gb : G)
    r.adjustment r.terminalAdjustment (hUV.trans hVH) hreverse hfaith hrank hequal
  dsimp only at hh
  rw [← r.conjugator_val] at hh
  exact ⟨r, hh⟩

/-- Construct all reversed source data in the equality case of 13.8.25.

The only uniform inputs are the earlier F.9.11/13/15 statements and the
complete generation implication 13.8.18(1), whose standing source hypotheses
are discharged by the caller. In particular the latter quantifies over the
actual endpoint group and edge and over every F≤U_H outside its literal D_H.
The input `S` is intrinsic to the fixed base edge. After normalizing the
reversed edge, its same W, natural head and irreducible I remain available;
`eligible_of_rank_and_equality` proves all new actor-specific conditions.
No fixed-pair nonsplitting or marked conclusion is treated as uniform.

The returned equivalence is the precise final transport the parent uses:
apply `Eligible.forward` to the constructed eligibility, and then negate
this equivalence to obtain A₁ ≰ U_H. Equality-case fixation and the final
13.8.25 contradiction remain in the parent. -/
theorem exists_eligible_reversal [Finite G] [FiniteDimensional (ZMod 2) U]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (V₃ V₁ : Subgroup G) (S : SourceData L T H V V₃ V₁ ρ)
    (c : CriticalPair L T H V)
    (hgeo : ∀ d : CriticalPair L T H V,
      CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry d V₃ V₁)
    (hcore : ∀ d : CriticalPair L T H V,
      d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (generation18 : ∀ d : CriticalPair L T H V, ∀ F ≤ Source.UH H V₃,
      ¬ F ≤ Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone V₁) →
      vertexGroup L T H d.gamma = conjugateSpanBy F (vertexGroup L T H d.gamma) ⊔
        edgeGroup L T H d.gamma d.previous)
    (hrank : 1 < rank (Source.starImage H (c.Ugamma V₃)))
    (hequal : Module.finrank (ZMod 2)
      (U ⧸ S.sectionModel.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))) =
      rank (Source.starImage H (c.Ugamma V₃))) :
    ∃ r : Reversal c, Eligible S r.pair ∧
      (V₁ ≤ r.pair.Ugamma V₃ ↔ c.Aone V₁ ≤ Source.UH H V₃) := by
  have hUV : c.Ugamma V₃ ≤ c.Vgamma :=
    map_mono (conjugateSpanBy_mono S.seed_le le_rfl)
  have hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom := by
    rw [← c.vertexGroup_gamma]
    exact (conjugateSpanBy_mono S.seed_le le_rfl).trans (hgeo c).VH_endpoint
  obtain ⟨r, hr, he⟩ := exists_numerically_eligible_reversal V₃ V₁ c S.sectionModel
    S.faithful (hgeo c).length hUV (hgeo c).Vgamma_H (hgeo c).first_kernel hreverse hrank hequal
  exact ⟨r, eligible_of_rank_and_equality S r.pair (hgeo r.pair) (hcore r.pair)
    (generation18 r.pair) hr he, r.line_containment V₃ V₁ S.sectionModel⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData

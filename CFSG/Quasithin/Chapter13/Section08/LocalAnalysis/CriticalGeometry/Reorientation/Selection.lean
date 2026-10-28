module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Geometry

/-!
# Selecting a critical pair with the required rank comparison

The construction chooses the original pair or its genuine geodesic reversal.
The adjusted conjugator exchanges the two denominator ranks, so comparison
of the two natural numbers makes the choice. Both strict denominators survive.
The selected star subgroup is nontrivial and elementary abelian. The explicit
earlier quadratic-action conclusion 13.8.4(6) and F.9.16(2)'s estimate give
membership in Q(H*,Ũ_H), retaining fixedCodim≤2*rank.

The representation is tied to the literal central section by a surjective
quotient map, exact kernel V₁ and the ambient conjugation equation. The
finite-dimensional section is therefore U_H/V₁, not an arbitrary model tag.
The earlier F.9.11/13/15 hypotheses remain explicit; rank selection itself
is constructed here and is not an input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.8(2),
printed p.949; F.9.16–17, printed pp.323–324; and D.2.1, printed p.178.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open PairConsequences ReversedSourceData
variable {G U : Type*} [Group G] [Finite G] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] {L T H V : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- D.2.1's Q-family, with its factor two rather than the FF-offender bound. -/
def QuadraticMember (ρ : Representation (ZMod 2) (Source.Hstar H) U)
    (A : Subgroup (Source.Hstar H)) : Prop :=
  IsElementaryTwo A ∧ IsQuadratic ρ A ∧ fixedCodim ρ A ≤ 2 * rank A

/-- The rank of the literal source quotient U_H/D_H. -/
noncomputable def denominatorRank (V₃ Z : Subgroup G) (c : CriticalPair L T H V) : ℕ :=
  Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z)).relIndex (Source.UH H V₃))

/-- Select between the actual pair and its constructed reversal. Both strict
denominators are preserved and the selected actor has the larger rank. -/
theorem exists_rank_selection
    (V₃ Z : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) Z ρ) (hfaith : Function.Injective ρ)
    (hb : 3 ≤ c.path.length) (hV₃ : V₃ ≤ V)
    (hVH : ∀ d : CriticalPair L T H V, d.Vgamma ≤ H)
    (hUend : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hF915 : c.Vgamma ⊓ firstKernel L T H (base L T H true) =
      Source.Egamma c.Vgamma (Source.UH H V₃) Z)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) < Source.UH H V₃)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z < c.Ugamma V₃) :
    ∃ d : CriticalPair L T H V,
      (d = c ∨ ∃ r : Reversal c, r.pair = d) ∧
      Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone Z) < Source.UH H V₃ ∧
      Source.Dgamma (d.Ugamma V₃) (Source.UH H V₃) Z < d.Ugamma V₃ ∧
      0 < rank (Source.starImage H (d.Ugamma V₃)) ∧
      denominatorRank V₃ Z d ≤ rank (Source.starImage H (d.Ugamma V₃)) := by
  have hγH (d : CriticalPair L T H V) : d.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans (hVH d)
  have hZ := s.centralizes.trans (centralizer_le_normalizer _)
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hp : 0 < rank (Source.starImage H (c.Ugamma V₃)) :=
    (show IsElementaryTwo (Source.starImage H (c.Ugamma V₃)) from
      ⟨starImage_ne_bot_of_Dgamma_lt H (Source.UH H V₃) (c.Ugamma V₃) Z (hγH c)
        (s.Dgamma_eq_inf_core _ (hγH c) hfaith) hDγ,
        starImage_isElementaryAbelian H (c.Ugamma V₃) (hγH c)⟩).rank_pos
  by_cases hc : denominatorRank V₃ Z c ≤ rank (Source.starImage H (c.Ugamma V₃))
  · exact ⟨c, Or.inl rfl, hDH, hDγ, hp, hc⟩
  obtain ⟨r⟩ := exists_reversal_of_strict c V₃ Z hb hV₃ (hVH c) hZ hF915 hDγ
  have hUA : Source.UH H V₃ ≤ normalizer (c.Aone Z) := by
    have hn := map_mono (f := (MulAut.conj (c.gb : G)).toMonoidHom) hZ
    rw [map_equiv_normalizer_eq, ← c.vertexGroup_gamma] at hn
    exact hUend.trans hn
  obtain ⟨hrD, hrDγ⟩ := denominators r V₃ Z hZ (hγH c) hUA
  have hsD : Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone Z) <
      Source.UH H V₃ := by
    rw [hrD]
    have hs := (map_lt_map_iff_of_injective
      (f := (MulAut.conj (transporter r : G)).toMonoidHom)
      (MulAut.conj (transporter r : G)).injective).mpr hDγ
    exact hs.trans_eq (return_map r (Source.UH H V₃) s.normalizes)
  have hsDγ : Source.Dgamma (r.pair.Ugamma V₃) (Source.UH H V₃) Z < r.pair.Ugamma V₃ := by
    rw [hrDγ]
    have hs := (map_lt_map_iff_of_injective
      (f := (MulAut.conj (transporter r : G)).toMonoidHom)
      (MulAut.conj (transporter r : G)).injective).mpr hDH
    exact hs.trans_eq (endpoint_map r (Source.UH H V₃) s.normalizes).symm
  have hback : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom := by
    rwa [← c.vertexGroup_gamma]
  obtain ⟨hr, hd⟩ := adjusted_rank_and_codimension s (c.gb : G)
    r.adjustment r.terminalAdjustment (hγH c) hback hfaith
  rw [← r.conjugator_val] at hr hd
  change rank (Source.starImage H (r.pair.Ugamma V₃)) =
    Module.finrank (ZMod 2) (U ⧸ s.image
      (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z))) at hr
  change Module.finrank (ZMod 2) (U ⧸ s.image
    (Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone Z))) = _ at hd
  rw [s.quotient_finrank _ (s.line_le_DH _ _ (hγH c))] at hr
  rw [s.quotient_finrank _ (s.line_le_DH _ _ (hγH r.pair))] at hd
  change rank (Source.starImage H (r.pair.Ugamma V₃)) = denominatorRank V₃ Z c at hr
  change denominatorRank V₃ Z r.pair = rank (Source.starImage H (c.Ugamma V₃)) at hd
  exact ⟨r.pair, Or.inr ⟨r, rfl⟩, hsD, hsDγ, by omega, by omega⟩

/-- F.9.16(2) is applied after constructing the selected critical pair.
Quadratic action and the full factor-two estimate are retained. -/
theorem exists_quadratic_selection
    (V₃ Z : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) Z ρ) (hfaith : Function.Injective ρ)
    (hb : 3 ≤ c.path.length) (hV₃ : V₃ ≤ V)
    (hVH : ∀ d : CriticalPair L T H V, d.Vgamma ≤ H)
    (hUend : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hF915 : c.Vgamma ⊓ firstKernel L T H (base L T H true) =
      Source.Egamma c.Vgamma (Source.UH H V₃) Z)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) < Source.UH H V₃)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z < c.Ugamma V₃)
    (hquadratic : ∀ d : CriticalPair L T H V, IsQuadratic ρ (Source.starImage H (d.Ugamma V₃)))
    (hF916 : ∀ d : CriticalPair L T H V,
      0 < rank (Source.starImage H (d.Ugamma V₃)) →
      denominatorRank V₃ Z d ≤ rank (Source.starImage H (d.Ugamma V₃)) →
      fixedCodim ρ (Source.starImage H (d.Ugamma V₃)) ≤
        2 * rank (Source.starImage H (d.Ugamma V₃))) :
    ∃ d : CriticalPair L T H V,
      Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone Z) < Source.UH H V₃ ∧
      Source.Dgamma (d.Ugamma V₃) (Source.UH H V₃) Z < d.Ugamma V₃ ∧
      0 < rank (Source.starImage H (d.Ugamma V₃)) ∧
      denominatorRank V₃ Z d ≤ rank (Source.starImage H (d.Ugamma V₃)) ∧
      QuadraticMember ρ (Source.starImage H (d.Ugamma V₃)) := by
  obtain ⟨d, _, hd, hdγ, hp, hc⟩ := exists_rank_selection V₃ Z c s hfaith hb hV₃
    hVH hUend hF915 hDH hDγ
  let _ : IsElementaryAbelian 2 (d.Ugamma V₃) := IsElementaryAbelian.map _
  have he : IsElementaryAbelian 2 (Source.starImage H (d.Ugamma V₃)) :=
    starImage_isElementaryAbelian H (d.Ugamma V₃)
      ((map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans (hVH d))
  have hn : Source.starImage H (d.Ugamma V₃) ≠ ⊥ := by
    intro hz
    simp [hz, rank] at hp
  exact ⟨d, hd, hdγ, hp, hc, ⟨hn, he⟩, hquadratic d, hF916 d hp hc⟩

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
end

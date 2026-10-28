module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Selection

/-!
# The corrected complete geometric alternatives in 13.8.8

Split on the two actual denominators. In a full-denominator case the ambient
commutators construct a nontrivial transvection group and an actual nonidentity
actor, which triggers the complete earlier 13.8.5 conclusion. In the strict
case compare the two denominator ranks and, when necessary, construct the
reversed critical pair. F.9.16(2) supplies its factor-two codimension estimate.
Incidence then constructs h∈H taking γ₂ to γ₀; F.9.13(1),(2) transport Vγ
into the intrinsic two-core of L₁T, and hence R₁.

`alternatives_corrected` is deliberately distinct from a literal transcription
of 13.8.8(1). Its returned vertex is g_b⁻¹γ₁, not the printed g_b⁻¹γ=γ₁.
It states the proof-supported actors explicitly: Uα or Vα in the full-Dγ
case, and Uγ in the remaining full-D_H case. In the commuting case the
earlier centralizer bound enlarges the returned seed V to the full Vα.
No identification of different vertices or of Uγ with Vγ is used.

Earlier inputs, to be supplied by the source assembly owner:
* the genuine central quotient action and its faithful H/O₂(H) realization,
  elementary U_H, V₃≤V, and |V₁|=2 (13.5/13.7 and F.9.2);
* `EarlierGeometry` uniformly for critical pairs (F.9.11,13,15), together
  with the noncentrality in F.9.13(5) for the initial pair;
* [V_H,H_C]≤V₁ (13.7.3(7)) and the entire implication 13.8.5(1)–(3);
* quadratic action (13.8.4(6)) and the estimate in F.9.16(2), uniformly;
* the standard edge identity and endpoint-in-edge-core containment
  (F.9.13(1),(2)), and O₂(L₁T)≤R₁ in the standing flag setup.
Selection, strictness, the positive rank, actual actors and the element h
are proved here, not included in the inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.8,
printed p.949 (PDF p.966), and F.9.13–17, printed pp.322–324.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
open AsymmetricPair
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open PairConsequences.ReversedSourceData
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] {L T H V : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) E}

/-- The corrected actors at the actual vertices α=g_b⁻¹γ₁ and γ. -/
def TransvectionAlternative (c : CriticalPair L T H V) (V₃ Z : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [(Z.subgroupOf (Source.UH H V₃)).Normal]
    (Q : CenterQuotientAction H (Source.UH H V₃) Z) : Prop :=
  (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z = c.Ugamma V₃ ∨
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) = Source.UH H V₃) ∧
  (TransvectionGroup Q (Ualpha c V₃) ∨ TransvectionGroup Q (Valpha c) ∨
    TransvectionGroup Q (c.Ugamma V₃))

/-- The full strict-denominator output, for an actually selected critical pair. -/
def SelectedAlternative (L₁ R₁ V₃ Z : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) E) : Prop :=
  ∃ d : CriticalPair L T H V,
    Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone Z) < Source.UH H V₃ ∧
    Source.Dgamma (d.Ugamma V₃) (Source.UH H V₃) Z < d.Ugamma V₃ ∧
    0 < rank (Source.starImage H (d.Ugamma V₃)) ∧
    denominatorRank V₃ Z d ≤ rank (Source.starImage H (d.Ugamma V₃)) ∧
    QuadraticMember ρ (Source.starImage H (d.Ugamma V₃)) ∧
    ∃ h : H, inG0 (L := L) (T := T) h • d.second = base L T H false ∧
      d.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2 ∧
      (L₁ ⊔ T).pCoreIn 2 ≤ R₁

/-- The two alternatives of 13.8.8 with the vertex/actor correction recorded
above. No extra source conclusions have been discarded from 13.8.5. -/
theorem alternatives_corrected
    (c : CriticalPair L T H V) (L₁ R₁ V₃ Z : Subgroup G) (hL₁ : L₁ ≤ H)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [(Z.subgroupOf (Source.UH H V₃)).Normal]
    (Q : CenterQuotientAction H (Source.UH H V₃) Z)
    (s : ConjugationSection H (Source.UH H V₃) Z ρ) (hfaith : Function.Injective ρ)
    (hV₃ : V₃ ≤ V) (hcard : Nat.card Z = 2)
    (hgeo : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ Z)
    (hbad : ¬ ⁅c.Ugamma V₃, V⁆ ≤ c.Aone Z)
    (hcentral : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ Z)
    (hmodels : (∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
      LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ Z))) →
      FullModelConclusions L L₁ T hL₁ Q)
    (hquadratic : ∀ d : CriticalPair L T H V, IsQuadratic ρ (Source.starImage H (d.Ugamma V₃)))
    (hF916 : ∀ d : CriticalPair L T H V,
      0 < rank (Source.starImage H (d.Ugamma V₃)) →
      denominatorRank V₃ Z d ≤ rank (Source.starImage H (d.Ugamma V₃)) →
      fixedCodim ρ (Source.starImage H (d.Ugamma V₃)) ≤
        2 * rank (Source.starImage H (d.Ugamma V₃)))
    (hedge : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hcore : ∀ d : CriticalPair L T H V,
      d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (hR : (L₁ ⊔ T).pCoreIn 2 ≤ R₁) :
    (TransvectionAlternative c V₃ Z Q ∧ FullModelConclusions L L₁ T hL₁ Q) ∨
      SelectedAlternative (L := L) (T := T) (V := V) L₁ R₁ V₃ Z ρ := by
  have hZ := s.centralizes.trans (centralizer_le_normalizer _)
  have hUV : Source.UH H V₃ ≤ Source.VH H V := conjugateSpanBy_mono hV₃ le_rfl
  have hγH : c.Ugamma V₃ ≤ H := (map_mono hUV).trans (hgeo c).Vgamma_H
  have hUend := hUV.trans (hgeo c).VH_endpoint
  have hUA : Source.UH H V₃ ≤ normalizer (c.Aone Z) := by
    have hn := map_mono (f := (MulAut.conj (c.gb : G)).toMonoidHom) hZ
    rw [map_equiv_normalizer_eq, ← c.vertexGroup_gamma] at hn
    exact hUend.trans hn
  have hmodel_of {P : Subgroup G} (ht : TransvectionGroup Q P) :
      FullModelConclusions L L₁ T hL₁ Q := by
    obtain ⟨t, _, hn, ht⟩ := ht.nonidentity_actor
    exact hmodels ⟨t, hn, ht⟩
  by_cases hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z < c.Ugamma V₃
  · by_cases hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) < Source.UH H V₃
    · obtain ⟨d, hd, hdγ, hp, hc, hQ⟩ := exists_quadratic_selection V₃ Z c s hfaith
        (hgeo c).length hV₃ (fun d => (hgeo d).Vgamma_H) hUend (hgeo c).first_kernel
        hDH hDγ hquadratic hF916
      obtain ⟨h, hh, hv, _⟩ := exists_second_to_base d L₁ R₁
        (by have := (hgeo d).length; omega) hedge (hcore d) hR
      exact Or.inr ⟨d, hd, hdγ, hp, hc, hQ, h, hh, hv, hR⟩
    · have he := eq_of_le_of_not_lt (commutatorPreimage_le (Source.UH H V₃)
        (c.Ugamma V₃) (c.Aone Z)) hDH
      have ht := transvection_of_DH_eq_Dgamma_lt c V₃ Z Q hcard hγH hUA
        (hgeo c).lines_disjoint he hDγ
      exact Or.inl ⟨⟨Or.inr he, Or.inr (Or.inr ht)⟩, hmodel_of ht⟩
  · have he := eq_of_le_of_not_lt (commutatorPreimage_le (c.Ugamma V₃)
      (Source.UH H V₃) Z) hDγ
    rcases transvection_of_Dgamma_eq c V₃ Z Q hV₃ hZ hcard hγH
      (hgeo c).VH_endpoint hUA (hgeo c).lines_disjoint hcentral hbad he with ht | ht
    · exact Or.inl ⟨⟨Or.inl he, Or.inl ht⟩, hmodel_of ht⟩
    · exact Or.inl ⟨⟨Or.inl he, Or.inr (Or.inl ht)⟩, hmodel_of ht⟩

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
end

module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Transport of the asymmetric critical pair

The actual denominator definitions force the commutator to be the central
line: it is contained in V₁, and strictness of D_H makes it nontrivial.
Conjugation by the inverse of the critical-pair endpoint element transports
this to [U_H,Uα]=V₁^g. The two F.9 kernel identities transport to the unequal
two-core containments used in the interchange argument.

All maps use left conjugation. Thus `returnElement` is the inverse of the
published endpoint conjugator; it sends γ back to γ₁. No symmetry or model
classification is assumed here. The kernel identities are the precise
consequences of F.9.2(3) and F.9.13 used below, supplied by the source owner.

Source: Aschbacher–Smith, 13.8.7, printed pp.948–949.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
variable {G : Type*} [Group G]

/-- The source g, expressed in the left-conjugation convention. -/
def returnElement {L T H V : Subgroup G} (c : CriticalPair L T H V) : G0 L T H :=
  c.gb⁻¹

/-- The transported endpoint γ₁^g. -/
def alpha {L T H V : Subgroup G} (c : CriticalPair L T H V) : Vertex L T H :=
  returnElement c • base L T H true

def Ualpha {L T H V : Subgroup G} (c : CriticalPair L T H V)
    (V₃ : Subgroup G) : Subgroup G :=
  (Source.UH H V₃).conjBy (returnElement c : G)

def Qalpha {L T H V : Subgroup G} (c : CriticalPair L T H V) : Subgroup G :=
  (Source.QH H).conjBy (returnElement c : G)

/-- The kernel of Uα in the actual quotient H/O₂(H). -/
def Dalpha {L T H V : Subgroup G} (c : CriticalPair L T H V)
    (V₃ : Subgroup G) : Subgroup G := Ualpha c V₃ ⊓ Source.QH H

def centerAlpha {L T H V : Subgroup G} (c : CriticalPair L T H V)
    (V₁ : Subgroup G) : Subgroup G := V₁.conjBy (returnElement c : G)

theorem returnElement_gamma {L T H V : Subgroup G} (c : CriticalPair L T H V) :
    returnElement c • c.gamma = base L T H true := by
  rw [← c.gb_one]
  exact inv_smul_smul c.gb _

theorem vertexGroup_alpha {L T H V : Subgroup G} (c : CriticalPair L T H V) :
    vertexGroup L T H (alpha c) = H.conjBy (returnElement c : G) := by
  rw [alpha, vertexGroup_smul, vertexGroup_base]
  rfl

/-- F.9.16(1i)'s commutator equality directly from the actual denominators. -/
theorem commutator_eq_line_of_asymmetry [Finite G]
    (U Uγ V₁ A₁ : Subgroup G) (hcard : Nat.card V₁ = 2)
    (hn : Uγ ≤ normalizer (V₁ : Set G))
    (hstrict : Source.DH U Uγ A₁ < U)
    (hfull : Source.Dgamma Uγ U V₁ = Uγ) : ⁅U, Uγ⁆ = V₁ := by
  have hle : ⁅U, Uγ⁆ ≤ V₁ := by
    rw [commutator_comm, ← hfull]
    exact commutator_commutatorPreimage_le Uγ U V₁ hn
  have hne : ⁅U, Uγ⁆ ≠ ⊥ := by
    intro he
    apply hstrict.not_ge
    exact le_commutatorPreimage le_rfl (he ▸ bot_le)
  have hdiv : Nat.card (⁅U, Uγ⁆ : Subgroup G) ∣ 2 := hcard ▸ card_dvd_of_le hle
  have hc : Nat.card (⁅U, Uγ⁆ : Subgroup G) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (fun hh => hne (card_eq_one.mp hh))
  exact eq_of_le_of_card_ge hle (by rw [hcard, hc])

/-- The inverse endpoint transports the line and both unequal kernel containments.
The only geometry inputs beyond the denominators are F.9's actual kernel
identities and the disjointness of its two central lines. -/
theorem transported_configuration [Finite G]
    {L T H V : Subgroup G} (c : CriticalPair L T H V) (V₃ V₁ : Subgroup G)
    (hcard : Nat.card V₁ = 2)
    (hn : c.Ugamma V₃ ≤ normalizer (V₁ : Set G))
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) <
      Source.UH H V₃)
    (hfull : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) =
      Source.UH H V₃ ⊓ c.Qgamma)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hdisj : V₁ ⊓ c.Aone V₁ = ⊥) :
    ⁅Source.UH H V₃, Ualpha c V₃⁆ = centerAlpha c V₁ ∧
      Source.UH H V₃ ≤ Qalpha c ∧ ¬ Ualpha c V₃ ≤ Source.QH H ∧
      centerAlpha c V₁ ⊓ V₁ = ⊥ := by
  have hU : (c.Ugamma V₃).conjBy (returnElement c : G) = Source.UH H V₃ := by
    exact conjBy_inv (Source.UH H V₃) (c.gb : G)
  have hQ : c.Qgamma.conjBy (returnElement c : G) = Source.QH H := by
    exact conjBy_inv (Source.QH H) (c.gb : G)
  have hA : (c.Aone V₁).conjBy (returnElement c : G) = V₁ := by
    exact conjBy_inv V₁ (c.gb : G)
  have hc := congrArg (fun X : Subgroup G => X.conjBy (returnElement c : G))
    (commutator_eq_line_of_asymmetry (Source.UH H V₃) (c.Ugamma V₃)
      V₁ (c.Aone V₁) hcard hn hstrict hfull)
  have hc' : ⁅Ualpha c V₃, Source.UH H V₃⁆ = centerAlpha c V₁ := by
    change (⁅Source.UH H V₃, c.Ugamma V₃⁆).map _ = _ at hc
    rw [map_commutator] at hc
    change ⁅Ualpha c V₃, (c.Ugamma V₃).conjBy (returnElement c : G)⁆ = _ at hc
    rwa [hU] at hc
  refine ⟨(commutator_comm _ _).trans hc', ?_, ?_, ?_⟩
  · have hle : c.Ugamma V₃ ≤ Source.QH H := by
      rw [← hfull, hDγ]
      exact inf_le_right
    have hh := map_mono (f := (MulAut.conj (returnElement c : G)).toMonoidHom) hle
    change (c.Ugamma V₃).conjBy (returnElement c : G) ≤ Qalpha c at hh
    rwa [hU] at hh
  · intro hle
    have hh := map_mono (f := (MulAut.conj (c.gb : G)).toMonoidHom) hle
    have hback : (Ualpha c V₃).conjBy (c.gb : G) = Source.UH H V₃ :=
      conjBy_inv' (Source.UH H V₃) (c.gb : G)
    change (Ualpha c V₃).conjBy (c.gb : G) ≤ c.Qgamma at hh
    rw [hback] at hh
    exact hstrict.not_ge (hDH ▸ le_inf le_rfl hh)
  · have hh := congrArg (fun X : Subgroup G =>
        X.map (MulAut.conj (returnElement c : G)).toMonoidHom) hdisj
    rw [map_inf _ _ _ (MulAut.conj (returnElement c : G)).injective,
      Subgroup.map_bot] at hh
    change centerAlpha c V₁ ⊓ (c.Aone V₁).conjBy (returnElement c : G) = ⊥ at hh
    rwa [hA] at hh


/-- Transport of F.9.13(7): the whole U_H centralizes the transported kernel
when Dγ=Uγ. This is the centralization used in the cover branch. -/
theorem transported_denominator_centralizes
    {L T H V : Subgroup G} (c : CriticalPair L T H V) (V₃ V₁ : Subgroup G)
    (hfull : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) =
      Source.UH H V₃ ⊓ c.Qgamma)
    (hcross : ⁅Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁),
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁⁆ = ⊥) :
    ⁅Dalpha c V₃, Source.UH H V₃⁆ = ⊥ := by
  rw [hfull, hDH] at hcross
  have hh := congrArg (fun X : Subgroup G =>
    X.map (MulAut.conj (returnElement c : G)).toMonoidHom) hcross
  rw [map_commutator, map_inf _ _ _ (MulAut.conj (returnElement c : G)).injective,
    Subgroup.map_bot] at hh
  have hU : (c.Ugamma V₃).conjBy (returnElement c : G) = Source.UH H V₃ :=
    conjBy_inv (Source.UH H V₃) (c.gb : G)
  have hQ : c.Qgamma.conjBy (returnElement c : G) = Source.QH H :=
    conjBy_inv (Source.QH H) (c.gb : G)
  change ⁅Ualpha c V₃ ⊓ c.Qgamma.conjBy (returnElement c : G),
    (c.Ugamma V₃).conjBy (returnElement c : G)⁆ = ⊥ at hh
  simpa only [hU, hQ, Dalpha] using hh

/-- F.9.13's containment in the endpoint group transports into the base H. -/
theorem return_conjugate_le_H
    {L T H V : Subgroup G} (c : CriticalPair L T H V) (X : Subgroup G)
    (hX : X ≤ vertexGroup L T H c.gamma) :
    X.conjBy (returnElement c : G) ≤ H := by
  rw [c.vertexGroup_gamma] at hX
  have hh := map_mono (f := (MulAut.conj (returnElement c : G)).toMonoidHom) hX
  change X.conjBy (returnElement c : G) ≤ (H.conjBy (c.gb : G)).conjBy
    (c.gb : G)⁻¹ at hh
  rwa [conjBy_inv] at hh

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
end

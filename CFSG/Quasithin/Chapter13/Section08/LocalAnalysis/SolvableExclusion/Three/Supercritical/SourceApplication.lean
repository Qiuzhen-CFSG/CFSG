module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Assembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.FinalAssembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.SourceActions

/-!
# Applying the odd reduction to the earlier source geometry

The source identity C_H(U_H/V₁)=O₂(H) constructs a faithful action of the
literal H/O₂(H) on the literal quotient U_H/V₁. Its canonical quotient map
and conjugation equation give the section used by the critical geometry.
The complete 13.8.8 alternatives are then obtained from their proved
producer. Solvability excludes the first alternative, since the full
13.8.5 conclusion supplies a nonsolvable C-component of H. The second
alternative selects the actual pair, quadratic actor and h ∈ H placing
Vγ^h in O₂(L₁T). `exists_reducedOdd` now constructs the small odd subgroup,
its irreducible Frattini action and its prime-three-or-five restriction.

The explicit earlier inputs are the standing elementary flag and centralizer
identity, the full 13.8.5 implication, F.9.11/13/15 geometry and F.9.16(2)
estimate, 13.7.3(7), and the exact 13.8.12 residual alternative. The producers
are `CriticalGeometry.FinalAssembly.alternatives_from_earlier_inputs` (in
namespace `CriticalGeometry.Reorientation`) and the source standing-setup
assembly. The full 13.8.5 implication and F.9.16 estimate are expressed for
all realizations of the literal action, which are equal by
`Five.StarAction.action_eq`. No faithfulness, selection, quadraticity,
minimal offender movement, rank-two structure, or irreducibility premise
remains. The universal D.2.13(1) implication is the authorized Appendix input.

This proves the supercritical reduction, not the later three- and five-primary
exclusions or the entire solvable-overgroup theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), standing setup
on p.946, 13.8.4–11 on pp.947–950, and 13.8.13 on pp.950–951.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical
open CriticalGeometry CriticalGeometry.Reorientation
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Five.Localization.EndpointGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

private noncomputable def literalSection {H V₃ V₁ : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (a : Five.StarAction H (Source.UH H V₃) V₁)
    (hV₃ : V₃ ≤ H) (hV₁ : V₁ ≤ Source.UH H V₃)
    (hc : H ≤ centralizer (V₁ : Set G)) :
    ConjugationSection H (Source.UH H V₃) V₁ (Offenders.linearAction a) where
  le := conjugateSpanBy_le_self hV₃
  normalizes := a.normalizes
  centralizes := hc
  line_le := hV₁
  quotient := MulEquiv.toMultiplicative_toAdditive.symm.toMonoidHom.comp
    (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))
  surjective := MulEquiv.toMultiplicative_toAdditive.symm.surjective.comp
    (QuotientGroup.mk'_surjective _)
  kernel := by
    ext x
    change (Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) x)) = 1) ↔ _
    exact QuotientGroup.eq_one_iff x
  conjugates := a.conjugation

/-- Construct the faithful quotient action, select the genuine quadratic
critical endpoint using the complete earlier alternatives, and obtain the
small odd reduction for its actual conjugate Vα. -/
theorem exists_selected_reducedOdd
    (hD213 : Offenders.D213PrimeRestriction.{u, u})
    {H L L₁ L₁plus T G₁ M V V₃ V₁ R₁ : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (c : CriticalPair L T H V)
    (hs : Group.IsSolvable H) (hr : IsStronglyQuasithin H)
    (hH : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hV₃ : V₃ ≤ V) (hVT : V ≤ T) (hline : V₁ ≤ V₃) (hcard : Nat.card V₁ = 2)
    (hG₁ : G₁ ≤ centralizer (V₁ : Set G))
    (hk : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁)
    (hres : ResidualAlternative L L₁ L₁plus (residualInM H M)) (hplus : L₁plus ≤ L₁)
    (hgeo : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ V₁)
    (hbad : ¬ ⁅c.Ugamma V₃, V⁆ ≤ c.Aone V₁)
    (hcentral : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ V₁)
    (hmodels : ∀ a : Five.StarAction H (Source.UH H V₃) V₁,
      (∃ t : H, (centerAction a).action t ≠ 1 ∧
      binaryLinear ((centerAction a).action t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) →
      FullModelConclusions L L₁ T (le_sup_left.trans hH.prop.1.2) (centerAction a))
    (hF916 : ∀ a : Five.StarAction H (Source.UH H V₃) V₁,
      ∀ d : CriticalPair L T H V,
      0 < rank (Source.starImage H (d.Ugamma V₃)) →
      denominatorRank V₃ V₁ d ≤ rank (Source.starImage H (d.Ugamma V₃)) →
      fixedCodim (Offenders.linearAction a) (Source.starImage H (d.Ugamma V₃)) ≤
        2 * rank (Source.starImage H (d.Ugamma V₃)))
    (hedge : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hcore : ∀ d : CriticalPair L T H V,
      d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (hR : (L₁ ⊔ T).pCoreIn 2 ≤ R₁) :
    ∃ a : Five.StarAction H (Source.UH H V₃) V₁,
      Function.Injective a.action ∧ ∃ d : CriticalPair L T H V, ∃ h : H,
      d.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2 ∧
      QuadraticMember (Offenders.linearAction a) (Source.starImage H (d.Ugamma V₃)) ∧
      ∃ p, (p = 3 ∨ p = 5) ∧ Nonempty (ReducedOdd p H L₁ T M
        (d.Vgamma.map (MulAut.conj (h : G)).toMonoidHom)) := by
  have hV₃H := hV₃.trans (hVT.trans (le_sup_right.trans hH.prop.1.2))
  have hV₁U := hline.trans (le_conjugateSpanBy V₃ H)
  obtain ⟨a, ha⟩ := Five.exists_faithful_source_starAction H V₃ V₁
    ((hH.prop.2.1.trans hG₁).trans (Subgroup.centralizer_le_normalizer _)) hk
  let s := literalSection a hV₃H hV₁U (hH.prop.2.1.trans hG₁)
  have hfaith := Offenders.linearAction_injective a (a.injective_of_kernel hk)
  have halt := alternatives_from_earlier_inputs c L₁ R₁ V₃ V₁
    (le_sup_left.trans hH.prop.1.2) (centerAction a) s hfaith hV₃ hcard hgeo hbad
    hcentral (hmodels a) (hF916 a) hedge hcore hR
  rcases halt with ⟨_, hmodel⟩ | ⟨d, _, _, _, _, hQ, h, _, hplace, _⟩
  · obtain ⟨K, hK, _⟩ := hmodel.1
    let _ := hs
    exact (hK.not_isSolvable inferInstance).elim
  · refine ⟨a, ha, d, h, hplace, hQ, ?_⟩
    have hne : V₁ ≠ ⊥ := by
      intro he
      have hh := hcard
      rw [he, Nat.card_unique] at hh
      contradiction
    have hp : IsPGroup 2 V₁ :=
      (IsElementaryAbelian.isPGroup 2 (Source.UH H V₃)).of_injective
        (inclusion hV₁U) (inclusion_injective hV₁U)
    exact exists_reducedOdd hD213 hs hr hne hp
      (hline.trans (hV₃.trans (hVT.trans le_sup_right)))
      (hG₁.trans (Subgroup.centralizer_le_normalizer _)) hH hres hplus d hV₃ h rfl hplace a hk hQ

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical

end

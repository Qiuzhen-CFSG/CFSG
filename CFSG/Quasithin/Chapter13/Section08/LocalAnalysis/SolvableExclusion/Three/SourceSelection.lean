module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Assembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.FinalAssembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.SourceActions

/-!
# Selecting the common geometry for the odd-primary case split

The literal quotient action and full 13.8.8 alternatives select one critical
pair together with its quadratic actor, strict denominators, rank comparison
and parabolic-core placement. These conclusions construct `RankOne.Geometry`
for precisely that pair. The terminal-edge bound follows from the index-two
flag, and 13.8.5 supplies the transvection implication used by the rank-one
exclusions. Thus `exists_selected_five_or_noncontained` applies the odd
construction and the two rank-one exclusions without assuming their geometry
or selection conclusions.

The explicit earlier inputs are the standing elementary flag and centralizer
identity, the complete 13.8.5 implication, F.9.11/13/15 geometry and F.9.16(2)
estimate, 13.7.3(7), 13.7.7 noncentrality, and the exact 13.8.12 residual
alternative. Universal D.2.13(1) is the permitted Appendix input. The two
noncontained three-primary branches remain explicit alternatives in the
output, not assumptions or asserted contradictions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), standing setup
on p.946, 13.8.4–11 on pp.947–950, and proof of 13.8.13 on pp.950–951.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three
open CriticalGeometry CriticalGeometry.Reorientation
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Five.Localization.EndpointGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

private noncomputable def literalSection {H V₃ V₁ : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : Five.StarAction H (Source.UH H V₃) V₁)
    (hV₃ : V₃ ≤ H) (hV₁ : V₁ ≤ Source.UH H V₃)
    (hc : H ≤ centralizer (V₁ : Set G)) :
    ConjugationSection H (Source.UH H V₃) V₁ (Supercritical.Offenders.linearAction a) where
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

/-- Select the actual critical pair, construct all geometric hypotheses of
the rank-one exclusions, and reduce to five or the two noncontained cases. -/
theorem exists_selected_five_or_noncontained
    (hD213 : Supercritical.Offenders.D213PrimeRestriction.{u, u})
    {H L L₁ L₁plus G₁ M V V₃ V₁ : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (c : CriticalPair L T H V)
    (hs : Group.IsSolvable H) (hr : IsStronglyQuasithin H)
    (hH : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hV₃ : V₃ ≤ V) (hVT : V ≤ T) (hline : V₁ ≤ V₃)
    (hcard : Nat.card V₁ = 2) (hV₃card : Nat.card V₃ = 8)
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
      fixedCodim (Supercritical.Offenders.linearAction a) (Source.starImage H (d.Ugamma V₃)) ≤
        2 * rank (Source.starImage H (d.Ugamma V₃)))
    (hedge : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hcore : ∀ d : CriticalPair L T H V,
      d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (hUcore : ∀ d : CriticalPair L T H V,
      Source.UH H V₃ ≤ (edgeGroup L T H d.gamma d.previous).pCoreIn 2)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hindex : V₃.relIndex V = 2)
    (hnorm : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G))
    (hLM : L₁ ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hTL : (T : Subgroup G) ≤ normalizer (L₁ : Set G))
    (hseed : V₃ ≤ ⁅V₃, L₁⁆ ⊔ V₁) :
    ∃ a : Five.StarAction H (Source.UH H V₃) V₁, Function.Injective a.action ∧
      ∃ d : CriticalPair L T H V, RankOne.Geometry d V₃ V₁ L₁ ∧
      QuadraticMember (Supercritical.Offenders.linearAction a)
        (Source.starImage H (d.Ugamma V₃)) ∧
      ∃ h : H,
        d.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2 ∧
        (Nonempty (ReducedFive H L₁ T M
          (d.Vgamma.map (MulAut.conj (h : G)).toMonoidHom)) ∨
        ∃ r : ReducedOdd 3 H L₁ T M (d.Vgamma.map (MulAut.conj (h : G)).toMonoidHom),
          ¬ Source.starImage H L₁ ≤ Source.starImage H r.P ∧
          ((IsElementaryAbelian 3 (Source.starImage H r.P) ∧
            Nat.card (Source.starImage H r.P) = 3 ^ 2) ∨
           (IsExtraspecial 3 (Source.starImage H r.P) ∧
            Nat.card (Source.starImage H r.P) = 3 ^ 3 ∧
            ∀ x : Source.starImage H r.P, x ^ 3 = 1))) := by
  have hVH := hVT.trans (le_sup_right.trans hH.prop.1.2)
  have hV₁U := hline.trans (le_conjugateSpanBy V₃ H)
  have hz := (hH.prop.2.1.trans hG₁).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨a, ha⟩ := Five.exists_faithful_source_starAction H V₃ V₁ hz hk
  let s := literalSection a (hV₃.trans hVH) hV₁U (hH.prop.2.1.trans hG₁)
  have hfaith := Supercritical.Offenders.linearAction_injective a ha
  have halt := alternatives_from_earlier_inputs c L₁ ((L₁ ⊔ T).pCoreIn 2) V₃ V₁
    (le_sup_left.trans hH.prop.1.2) (centerAction a) s hfaith hV₃ hcard hgeo hbad
    hcentral (hmodels a) (hF916 a) hedge hcore le_rfl
  rcases halt with ⟨_, hmodel⟩ | ⟨d, hDH, hDγ, _, hcomp, hQ, h, _, hplace, _⟩
  · obtain ⟨K, hK, _⟩ := hmodel.1
    let _ := hs
    exact (hK.not_isSolvable inferInstance).elim
  · let _ : IsElementaryAbelian 2 V :=
      IsElementaryAbelian.of_le (show V ≤ Source.VH H V from le_conjugateSpanBy V H)
    have hcorecomm : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁ := by
      rw [commutator_comm, hk]
      exact commutator_commutatorPreimage_le H (Source.UH H V₃) V₁ hz
    have g : RankOne.Geometry d V₃ V₁ L₁ := {
      seed_le := hV₃
      V_le := hVH
      line_le := hV₁U
      line_normalized := hz
      line_card := hcard
      Vgamma_le := (hgeo d).Vgamma_H
      placement := ⟨h, hplace⟩
      base_edge := hedge
      endpoint_core := hUcore d
      DH_kernel := (hgeo d).DH_kernel
      Dgamma_kernel := (hgeo d).Dgamma_kernel
      DH_strict := hDH
      Dgamma_strict := hDγ
      comparison := d.index_comparison_of_selected_rank V₃ V₁
        ((map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans (hgeo d).Vgamma_H)
        (hgeo d).Dgamma_kernel hcomp
      core_commutator := hcorecomm
      noncentral := hnoncentral
      edge_commutator := d.edge_commutator_le_of_flag V₃ hV₃ hindex hnoncentral hnorm }
    refine ⟨a, ha, d, g, hQ, h, hplace, ?_⟩
    exact exists_five_or_noncontained hD213 g hs hr hH hline hVT
      (hG₁.trans (Subgroup.centralizer_le_normalizer _)) hres hplus a hk hQ h rfl hplace
      (component_conclusion_of_full a (le_sup_left.trans hH.prop.1.2) (hmodels a))
      hLM hTM hTL hseed hV₃card

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three

end

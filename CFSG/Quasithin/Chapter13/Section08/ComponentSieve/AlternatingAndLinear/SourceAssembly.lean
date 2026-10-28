module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Models

/-!
# Conditional assembly of Aschbacher–Smith 13.8.24–25

`not_alternatingSeven_uniform` excludes the actual component quotient A₇
on every member of the local family. `source_linear_alternative` reduces
K/O₂(K) ≅ Lₙ(2), 3 ≤ n ≤ 5, to n = 4 and proves all the source clauses:
L/O₂(L) is the triple cover of A₆, with an actual isomorphism to the
hexacode carrier `Atlas.Codes.HexEvenAutomorphisms`; H/O₂(H) ≅ L₄(2), the whole U_H/V₁
is its four-dimensional natural module, and H = G₁.

The seven-point partition proof supplies the uniform exclusion required by
the genuine C-component overgroup argument. The binary reduction excludes
L₃, L₅ and the middle-node S₈ action before identifying H with G₁. The
triple-cover conclusion then selects the covered local action from the
earlier ordinary/covered dichotomy: an ordinary A₆ quotient has trivial
center, whereas the triple cover has center of order three.

Both cases of 13.8.8 are retained. In the transvection case, the complete
13.8.5 models and the order of H* select the four-dimensional model, whose
linear equivalence is transported to the supplied literal conjugation
action. In the strict case, the earlier critical-pair bounds feed the
chief-factor, cohomology, splitting and cyclic/noncyclic deductions of
`FourStructure`. The natural-module conclusion includes the actual group
and equivariant linear equivalences, not just a dimension calculation.

The theorem is conditional on the genuine preceding local, geometric and
appendix facts, including the uniform 13.8.21–23 inputs. The chapter owner
supplies these earlier facts. No A₇ exclusion, binary group reduction,
natural head, chief-factor conclusion or H = G₁ is an input here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.24–25, printed pp.958–962/PDF pp.975–979.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.SourceAssembly
open FourStructure.ChiefFactors FourStructure.ChiefFactors.Alignment
open FourStructure.CriticalTransfer.PairConsequences
open CriticalGeometry CriticalGeometry.AsymmetricPair CriticalGeometry.Reorientation
open LinearReduction.SourceReduction
open Chapter1.Section02.LocalModels
open Chapter2.ComponentRefinement.LieType.Binary
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem covered_setup {L L₁ T V V₁ V₃ G₁ M : Subgroup G}
    (groups : GroupFacts L L₁ T V V₁ V₃ G₁ M)
    (hc : IsAlternatingCover (L ⧸ pCore 2 L) 6) :
    SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
      Nonempty (LocalAction.NaturalSetup L T V V₁ V₃) := by
  obtain ⟨ez⟩ := hc.2.1
  have hz : Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
    rw [Nat.card_congr ez.toEquiv]
    exact Nat.card_zmod 3
  rcases groups.local_action with hd | h
  · obtain ⟨d⟩ := hd
    have he := Nat.card_congr (Subgroup.centerCongr d.model).toEquiv
    rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6))] at he
    rw [hz] at he
    norm_num at he
  · exact h

/-- The preceding geometry and appendix inputs used to join the two cases of
13.8.8 in the linear branch. In particular, no covered-A₆, L₄, H = G₁,
natural-head, chief-factor, whole-module splitting or actor-rank conclusion is assumed.
`transvection_models` is the complete earlier 13.8.5 implication, retaining
all three group/module alternatives on the literal conjugation section. -/
structure EarlierModuleGeometry
    {L T H V : Subgroup G} (c : CriticalPair L T H V)
    (K L₁ V₁ V₂ V₃ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁)) : Prop where
  seed_index : V₁.relIndex V₃ = 4
  seed_irreducible : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
    L₁ ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃
  V_le : V ≤ H
  line_card : Nat.card V₁ = 2
  edge : (L ⊔ T) ⊓ H = L₁ ⊔ T
  conjugated_normal : ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
    (vertexGroup L T H c.gamma)).Normal
  conjugated_residual : pResidual 2 ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
    (vertexGroup L T H c.gamma)) = ⊤
  conjugated_quasisimple : IsQuasisimple (Source.starImage (vertexGroup L T H c.gamma)
    (K.map (MulAut.conj (c.gb : G)).toMonoidHom))
  terminal_core : Source.UH H V₃ ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2
  core_commutator : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁
  noncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃
  flag_index : V₃.relIndex V = 2
  edge_normalizes : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G)
  geometry : ∀ b : CriticalPair L T H V, EarlierGeometry b V₃ V₁
  base_core : ∀ b : CriticalPair L T H V,
    b.Vgamma ≤ (edgeGroup L T H (base L T H true) b.second).pCoreIn 2
  offender_bound : ∀ b : CriticalPair L T H V,
    0 < rank (Source.starImage H (b.Ugamma V₃)) →
    denominatorRank V₃ V₁ b ≤ rank (Source.starImage H (b.Ugamma V₃)) →
    fixedCodim ρ (Source.starImage H (b.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (b.Ugamma V₃))
  transvection_models : ∀ (hL₁ : L₁ ≤ H)
    (Q : CenterQuotientAction H (Source.UH H V₃) V₁) (a : Source.Hstar H),
    a ≠ 1 → fixedCodim ρ (zpowers a) = 1 → FullModelConclusions L L₁ T hL₁ Q
  linear_modules : ∀ e : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace, LinearB4.{u} e
  centralizer_bound : ⁅Source.HC H V₃, Source.VH H V⁆ ≤ V₁
  middle_le_seed : V₂ ≤ V₃
  middle_index : V₁.relIndex V₂ = 2
  middle_stable : T ≤ normalizer (V₂ : Set G)
  seed_intersection : V ⊓ Source.UH H V₃ = V₃
  generation : ∀ b : CriticalPair L T H V, ∀ F ≤ Source.UH H V₃,
    ¬ F ≤ Source.DH (Source.UH H V₃) (b.Ugamma V₃) (b.Aone V₁) →
    vertexGroup L T H b.gamma = conjugateSpanBy F (vertexGroup L T H b.gamma) ⊔
      edgeGroup L T H b.gamma b.previous
  two_factor_splitting : FourStructure.SplittingCyclic.AxisExclusions.TwoFactorSplitting.{u, u}
    (Source.Hstar H)

section FirstCase
variable {L L₁ T H V K G₁ M V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  {ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁)}

omit [Finite G] in
private theorem literal_eq_source (Q : CenterQuotientAction H (Source.UH H V₃) V₁)
    (hρ : IsSourceAction H V₃ V₁ ρ) (h : H) (v : SourceSpace H V₃ V₁) :
    literalRepresentation Q h v = ρ (QuotientGroup.mk' (pCore 2 H) h) v := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  change Additive.ofMul (Q.action h (QuotientGroup.mk' _ x)) =
    ρ (QuotientGroup.mk' (pCore 2 H) h) (Additive.ofMul (sourceProjection H V₃ V₁ x))
  exact (congrArg Additive.ofMul (Q.apply_mk h x)).trans (hρ h x).symm

omit [Finite G] in
private theorem natural_of_full_models
    (Q : CenterQuotientAction H (Source.UH H V₃) V₁)
    (hρ : IsSourceAction H V₃ V₁ ρ) (hL₁ : L₁ ≤ H)
    (hm : FullModelConclusions L L₁ T hL₁ Q)
    (e : Source.Hstar H ≃* PSL 4) :
    ∃ eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace, IsNatural ρ eH := by
  have hc : Nat.card (Source.Hstar H) = 20160 := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have no_perm {n : ℕ} (hn : n = 6 ∨ n = 7)
      (f : Source.Hstar H ≃* Equiv.Perm (Fin n)) : False := by
    rw [Nat.card_congr f.toEquiv] at hc
    rcases hn with rfl | rfl <;>
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hc
  rcases hm.2 with ⟨⟨s⟩ | ⟨s⟩, _⟩ | ⟨⟨s⟩ | ⟨⟨s⟩, _⟩, _⟩
  · obtain ⟨s⟩ := s
    exact (no_perm (Or.inl rfl) s.groupEquiv).elim
  · obtain ⟨s⟩ := s
    exact (no_perm (Or.inl rfl) s.groupEquiv).elim
  · obtain ⟨s⟩ := s
    exact (no_perm (Or.inr rfl) s.groupEquiv).elim
  · refine ⟨s.groupEquiv, s.moduleEquiv, ?_⟩
    intro a v
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) a
    rw [← literal_eq_source Q hρ]
    exact s.intertwines h v

end FirstCase

private theorem binary_model {Y : Type*} [Group Y] {n : ℕ}
    (h : ClassicalGroup.IsPSL Y n 2) : Nonempty (Y ≃* PSL n) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact ⟨e.trans (Atlas.fieldEquivPSL n eF)⟩

/-- Conditional 13.8.24, uniformly on the local family used in 13.8.25.
The seven-point proof constructs both partition actions from these earlier
inputs; the uniform exclusion is not an additional premise of the assembly. -/
theorem not_alternatingSeven_uniform
    (L L₁ L₀ X T V V₁ V₃ G₁ M : Subgroup G)
    (seven : ∀ (J C : Subgroup G), J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent →
      Nonempty (Seven.SourceExclusion.LocalData L T J V C L₁ L₀ X G₁ M V₃ V₁))
    {H K : Subgroup G} (hH : H ∈ Source.Hz L₁ T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) :
    ¬ IsAlternating (K ⧸ pCore 2 K) 7 := by
  obtain ⟨d⟩ := seven H K hH hKH hK
  exact d.not_alternatingSeven

/-- Conditional 13.8.25, including the entire natural module and H = G₁.
Uniform earlier data supply 13.8.24 on every local overgroup; the genuine
C-component embedding argument then supplies H = G₁. The group reduction
also selects the covered local setup. The complete 13.8.5 models handle
case (1), while case (2) feeds the proved chief-factor and cyclic/noncyclic
arguments. Both group and module conclusions use actual equivalences. -/
theorem source_linear_alternative
    (L L₁ L₀ X V V₁ V₂ V₃ G₁ M : Subgroup G) (T : Sylow 2 G)
    (groups : GroupFacts L L₁ (T : Subgroup G) V V₁ V₃ G₁ M)
    (seven : ∀ (J C : Subgroup G), J ∈ Source.Hz L₁ (T : Subgroup G) G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent →
      Nonempty (Seven.SourceExclusion.LocalData L T J V C L₁ L₀ X G₁ M V₃ V₁))
    (modules : ∀ (J C : Subgroup G), J ∈ Source.Hz L₁ (T : Subgroup G) G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent → Nonempty (LocalModuleData L T J V C L₁ G₁ M V₃ V₁))
    {𝒦 : GroupClass.{u}} (embeddings : LinearReduction.Overgroup.EarlierEmbeddings 𝒦)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁))
    (hG₁ : G₁ = normalizer (V₁ : Set G)) (hV₁base : V₁ ≤ L₁ ⊔ (T : Subgroup G))
    {H K : Subgroup G} {n : ℕ}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (moduleFacts : ModuleFacts c K L₁ G₁ M V₃ V₁ ρ)
    (earlier : EarlierModuleGeometry c K L₁ V₁ V₂ V₃ ρ)
    {E : Type u} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (τ : Representation (ZMod 2) (Source.Hstar H) E)
    (upper : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (hH : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) :
    n = 4 ∧ IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      Nonempty (Source.Hstar H ≃* PSL 4) ∧
      (∃ (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
        (eU : SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] NaturalSpace),
        (∀ a v, eU (ρ a v) = eH a (eU v)) ∧
        Module.finrank (ZMod 2) (SourceSpace H V₃ V₁) = 4) ∧ H = G₁ := by
  have hA7 : ∀ {J C : Subgroup G}, J ∈ Source.Hz L₁ (T : Subgroup G) G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent → ¬ IsAlternating (C ⧸ pCore 2 C) 7 := by
    intro J C hJ hCJ hC
    exact not_alternatingSeven_uniform L L₁ L₀ X (T : Subgroup G) V V₁ V₃ G₁ M seven hJ hCJ hC
  have hline : V₁ ≠ ⊥ := by
    intro he
    have hc := earlier.line_card
    rw [he] at hc
    simp at hc
  have hp : IsPGroup 2 V₁ := isPGroup_iff_card_dvd_pow.mpr
    ⟨1, by rw [earlier.line_card]; norm_num⟩
  obtain ⟨eK⟩ := binary_model hmodel
  obtain ⟨hn, hcover, ⟨eH⟩, hHG⟩ := source_linear_reduction L L₁ V V₁ V₃ G₁ M T
    groups modules embeddings hQ hA7 hline hp hV₁base hG₁.le
    hH hKH hK hn₀ hn₁ hmodel
  obtain ⟨hc, ⟨d⟩⟩ := covered_setup groups hcover
  refine ⟨hn, hcover, ⟨d.cover⟩, ⟨eH⟩, ?_, hHG⟩
  by_cases ht : ∃ a : Source.Hstar H, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1
  · obtain ⟨a, ha, ht⟩ := ht
    obtain ⟨Q⟩ := exists_centerQuotientAction
      (H := H) (U := Source.UH H V₃) (Z := V₁) (le_normalizer_conjugateSpanBy V₃ H)
      (moduleFacts.central_denominator.trans (Subgroup.centralizer_le_normalizer _))
    obtain ⟨e, eU, heU⟩ := natural_of_full_models Q moduleFacts.source_action
      ((groups.base_le_component hH hKH hK).trans hKH)
      (earlier.transvection_models _ Q a ha ht) eH
    refine ⟨e, eU, heU, ?_⟩
    rw [eU.finrank_eq]
    simp [NaturalSpace]
  · have hs := moduleFacts.critical_cases.resolve_left ht
    have hntrans : ∀ a : Source.Hstar H, a ≠ 1 → fixedCodim ρ (zpowers a) ≠ 1 := by
      intro a ha h
      exact ht ⟨a, ha, h⟩
    have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
    have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
      ⟨T.subtype hTH, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩
    have hLK : one L T V₁ ≤ K := groups.local_definition ▸ groups.base_le_component hH hKH hK
    have hLM : one L T V₁ ≤ M :=
      (one_le L T V₁).trans (inf_le_left.trans groups.base_le_M)
    exact FourStructure.source_natural_module_of_strict_critical_pair
      H K M L V V₁ V₂ V₃ T d c ρ moduleFacts.source_action hKH hLK hLM
      (le_sup_right.trans groups.base_le_M) hK (groups.component_normal hH hKH hK)
      hT (groups.supplement hH hKH hK).symm hc (groups.covered_factor hc)
      (groups.local_definition ▸ groups.local_normal H hH) (groups.covered_normalizer hc)
      (hn ▸ eK) earlier.seed_index (groups.local_definition ▸ earlier.seed_irreducible)
      earlier.V_le moduleFacts.central_denominator earlier.line_card
      (groups.local_definition ▸ earlier.edge) earlier.conjugated_normal
      earlier.conjugated_residual earlier.conjugated_quasisimple earlier.terminal_core
      earlier.core_commutator earlier.noncentral earlier.flag_index earlier.edge_normalizes
      earlier.geometry earlier.base_core earlier.offender_bound hs.2.1 hs.2.2.1
      hs.2.2.2.1 (moduleFacts.larger_rank hntrans) earlier.linear_modules (hHG.trans hG₁)
      earlier.centralizer_bound earlier.middle_le_seed earlier.middle_index earlier.middle_stable
      earlier.seed_intersection earlier.generation earlier.two_factor_splitting τ upper

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.SourceAssembly

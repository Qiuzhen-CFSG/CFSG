module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.EndpointKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.NaturalEndpoints
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.EndpointModelBounds

/-!
# Reciprocal critical indices and actual linear endpoint models

The actual endpoint sections have faithful Sylow action and fixed-space
generation. The complete local quotient catalogue therefore supplies both
lower quadratic estimates. Mutual center placement gives quadraticity;
the reciprocal centralizer bounds then force equality and strictness.
The sharp-index model theorem excludes every nonlinear row at both ends.

No faithful-action, residual-fixed-space, model-selection or numerical
estimate is assumed. The literal quotient remains L/O₂(G_delta), and
both section denominators remain Ω₁(Z(L)). Natural coordinates and equality
of the defining fields are further Chapter 7 obligations. `EndpointSource`
constructs these sections and applies this theorem on the reduced F1.11 graph.

Source: DGS, *Groups and Graphs* (1985), (7.1), pp.126–127.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Subgroup.CosetGeometry.RankTwo
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem graph_endpoint_model {v : Vertex (family P)} {E : Subgroup G}
    (c : LocalRankOneData (stabilizer (family P) v) E)
    [((Q (family P) v).subgroupOf c.Pstar).Normal] :
    IsRankOneModel (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar) := by
  have hcore : (Q (family P) v).subgroupOf c.Pstar = pCore 2 c.Pstar := by
    rw [show Q (family P) v = c.Pstar.pCoreIn 2 from c.same_core.symm]
    exact comap_map_eq_self_of_injective c.Pstar.subtype_injective _
  let e := QuotientGroup.quotientMulEquivOfEq hcore
  cases c.quotient with
  | linear n hn he => exact .linear n hn (he.of_mulEquiv e)
  | suzuki m he => exact .suzuki m ⟨e.trans he.some⟩
  | projective_unitary n hn he => exact .projective_unitary n hn (he.of_mulEquiv e)
  | special_unitary n hn he =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨f⟩⟩ := he
    exact .special_unitary n hn ⟨F,hF,hfin,J,hcard,hconj,⟨e.trans f⟩⟩
  | dihedral he => exact .dihedral ⟨e.trans he.some⟩

/-- Both actual endpoint quotients are linear and all reciprocal estimates are sharp. -/
theorem graph_endpoint_sections_linear_and_sharp
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (E₀ E₁ : Subgroup G)
    (c₀ : LocalRankOneData (stabilizer (family P) v) E₀)
    (c₁ : LocalRankOneData (stabilizer (family P) w) E₁)
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer (family P) v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer (family P) w))
    [((Q (family P) v).subgroupOf c₀.Pstar).Normal]
    [((Q (family P) w).subgroupOf c₁.Pstar).Normal]
    {W₀ W₁ : Type*}
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (σ₀ : Representation (ZMod 2) (c₀.Pstar ⧸ (Q (family P) v).subgroupOf c₀.Pstar) W₀)
    (σ₁ : Representation (ZMod 2) (c₁.Pstar ⧸ (Q (family P) w).subgroupOf c₁.Pstar) W₁)
    (d₀ : BinaryConjugationSection c₀.Pstar (Z (family P) v)
      (Stellmacher.omegaOneCenterAmbient c₀.Pstar)
      (σ₀.comp (QuotientGroup.mk' ((Q (family P) v).subgroupOf c₀.Pstar))))
    (d₁ : BinaryConjugationSection c₁.Pstar (Z (family P) w)
      (Stellmacher.omegaOneCenterAmbient c₁.Pstar)
      (σ₁.comp (QuotientGroup.mk' ((Q (family P) w).subgroupOf c₁.Pstar)))) :
    let A₀ := ((Z (family P) w).subgroupOf c₀.Pstar).map
      (QuotientGroup.mk' ((Q (family P) v).subgroupOf c₀.Pstar))
    let A₁ := ((Z (family P) v).subgroupOf c₁.Pstar).map
      (QuotientGroup.mk' ((Q (family P) w).subgroupOf c₁.Pstar))
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (c₀.Pstar ⧸ (Q (family P) v).subgroupOf c₀.Pstar) 2 (2^n)) ∧
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (c₁.Pstar ⧸ (Q (family P) w).subgroupOf c₁.Pstar) 2 (2^n)) ∧
      IsQuadratic σ₀ A₀ ∧ IsQuadratic σ₁ A₁ ∧
      Nat.card A₀ = Nat.card A₁ ∧
      Nat.card (W₀ ⧸ fixedSpace σ₀ A₀) = Nat.card A₀ ∧
      Nat.card (W₁ ⧸ fixedSpace σ₁ A₁) = Nat.card A₁ ∧
      Nat.card (W₀ ⧸ fixedSpace σ₀ A₀) < Nat.card A₀ ^ 2 ∧
      Nat.card (W₁ ⧸ fixedSpace σ₁ A₁) < Nat.card A₁ ^ 2 := by
  let := finite_endpoints h
  let := graph_Z_elementary h v
  let := graph_Z_elementary h w
  let : Finite c₀.Pstar := Finite.of_injective (inclusion c₀.Pstar_le) (inclusion_injective _)
  let : Finite c₁.Pstar := Finite.of_injective (inclusion c₁.Pstar_le) (inclusion_injective _)
  let : Finite (Z (family P) v) := Finite.of_injective (inclusion d₀.section_le) (inclusion_injective _)
  let : Finite (Z (family P) w) := Finite.of_injective (inclusion d₁.section_le) (inclusion_injective _)
  let : Finite W₀ := Finite.of_surjective (fun z => (d₀.coordinates z).toAdd)
    (Multiplicative.toAdd.surjective.comp d₀.onto)
  let : Finite W₁ := Finite.of_surjective (fun z => (d₁.coordinates z).toAdd)
    (Multiplicative.toAdd.surjective.comp d₁.onto)
  let π₀ := QuotientGroup.mk' ((Q (family P) v).subgroupOf c₀.Pstar)
  let π₁ := QuotientGroup.mk' ((Q (family P) w).subgroupOf c₁.Pstar)
  let A₀ := ((Z (family P) w).subgroupOf c₀.Pstar).map π₀
  let A₁ := ((Z (family P) v).subgroupOf c₁.Pstar).map π₁
  have hi := source_noncommuting_critical_intersections h hB hS hc hne
  have h₁₀ : Z (family P) w ≤ c₀.Pstar := local_twoGroup_le_star c₀ ho₀ _
    (IsElementaryAbelian.isPGroup 2 _) (criticalPair_centers (family P) h.generate hc).1
  have h₀₁ : Z (family P) v ≤ c₁.Pstar := local_twoGroup_le_star c₁ ho₁ _
    (IsElementaryAbelian.isPGroup 2 _) (criticalPair_centers (family P) h.generate hi.1).1
  obtain ⟨T₀,hT₀⟩ := ((IsElementaryAbelian.isPGroup 2 (Z (family P) w)).comap_subtype
    (K := c₀.Pstar)).exists_le_sylow
  obtain ⟨T₁,hT₁⟩ := ((IsElementaryAbelian.isPGroup 2 (Z (family P) v)).comap_subtype
    (K := c₁.Pstar)).exists_le_sylow
  let S₀ := T₀.mapSurjective (f := π₀) (QuotientGroup.mk'_surjective _)
  let S₁ := T₁.mapSurjective (f := π₁) (QuotientGroup.mk'_surjective _)
  have hg₀ : GeneratedByFixedSpace σ₀ S₀ := local_section_generated _ _ c₀ ho₀ σ₀ π₀ d₀ T₀
  have hg₁ : GeneratedByFixedSpace σ₁ S₁ := local_section_generated _ _ c₁ ho₁ σ₁ π₁ d₁ T₁
  have hd₀ := graph_critical_endpoint_section_sylow_kernel h hB hS hc E₀ c₀ ho₀ σ₀ d₀ T₀
  have hd₁ := graph_critical_endpoint_section_sylow_kernel h hB hS hi.1 E₁ c₁ ho₁ σ₁ d₁ T₁
  have hq := critical_sections_quadratic c₀.Pstar c₁.Pstar _ _ _ _ σ₀ π₀ σ₁ π₁ d₀ d₁ h₁₀ h₀₁
  have hA₀ : 1 < Nat.card A₀ := A₀.one_lt_card_iff_ne_bot.mpr
    (quotient_actor_ne_bot c₀.Pstar _ _ _ h₁₀ (graph_Q_centralizes_Z h v) hne)
  have hA₁ : 1 < Nat.card A₁ := A₁.one_lt_card_iff_ne_bot.mpr
    (quotient_actor_ne_bot c₁.Pstar _ _ _ h₀₁ (graph_Q_centralizes_Z h w)
      (by rwa [commutator_comm]))
  have hb₀ := rankOne_sylow_faithful_quadratic_bound (graph_endpoint_model c₀)
    σ₀ S₀ A₀ (map_mono hT₀) hA₀ hq.1 hg₀ hd₀
  have hb₁ := rankOne_sylow_faithful_quadratic_bound (graph_endpoint_model c₁)
    σ₁ S₁ A₁ (map_mono hT₁) hA₁ hq.2 hg₁ hd₁
  have hr := reciprocal_section_indices c₀.Pstar c₁.Pstar _ _ _ _ _ _
    σ₀ π₀ σ₁ π₁ d₀ d₁ h₁₀ h₀₁ (QuotientGroup.ker_mk' _) (QuotientGroup.ker_mk' _)
    hi.2.1 hi.2.2 hne hb₀ hb₁
  exact ⟨rankOne_linear_of_sylow_faithful_sharp_index (graph_endpoint_model c₀)
      σ₀ S₀ A₀ (map_mono hT₀) hA₀ hq.1 hg₀ hd₀ hr.2.2.1.le,
    rankOne_linear_of_sylow_faithful_sharp_index (graph_endpoint_model c₁)
      σ₁ S₁ A₁ (map_mono hT₁) hA₁ hq.2 hg₁ hd₁ hr.2.2.2.1.le,
    hq.1,hq.2,hr.2⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting

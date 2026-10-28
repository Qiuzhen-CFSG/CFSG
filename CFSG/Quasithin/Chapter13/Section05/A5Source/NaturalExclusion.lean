module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.G2False
public import CFSG.Quasithin.Chapter13.Section05.A5Source.EightOrders

/-!
# Exclusion of the three natural quotients in the original A₅ source

The natural quotient on the actual selected component has three possible rows.
S₆ gives a chief count of three, contradicting the source parity bound. A₈ gives
orders 128 and 32, contradicting the source core bound. G₂(2)′ supplies an
order-four cubic fixed point inside the elementary second layer. All actions
and quotient maps are those of the original source configuration.
Source: Aschbacher–Smith13.5.22–25, printed pp.924–925.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open ComponentReduction Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
universe u
variable {G : Type u} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ : Subgroup G} [IsElementaryAbelian 2 D.V]
  (d : Context D.T D.L D.V D.V₁ V₂ D.Vplus) (h : D.Hypothesis)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T
    (centralizer (D.V₁ : Set G)) (normalizer (D.L : Set G)))
  (hU : ¬ IsMulCommutative D.UH)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
  (hnot : ¬ ModelConclusion G 5)
include d h hA312 hH hU hnot

private theorem symmetric_six_quotient_false
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (hn : (starImage D.H K).Normal)
    (f : Catalogue.actor D K ≃* Equiv.Perm (Fin 6))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2]
      Theory.SpecificGroups.SymmetricSix.NaturalModule)
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      fV (CentralQuotient.representation D h K hn b.val u) =
        BinaryDuadModule.naturalAction (f b) (fV u)) : False := by
  let q := Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison.naturalLinearEquiv
  let w := fV.trans q.symm
  apply symmetric_six_source_false d h hA312 hH hU hnot K s hLK f w
  intro b u
  apply q.injective
  change q (q.symm (fV (CentralQuotient.projection D h K
      (Action.starRepresentation D h b.val u)))) = _
  rw [q.apply_symm_apply,
    Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison.naturalLinearEquiv_equivariant,
    Theory.SpecificGroups.SymmetricSix.polarRepresentation_apply]
  change fV (CentralQuotient.projection D h K
    (Action.starRepresentation D h b.val u)) =
      BinaryDuadModule.naturalAction (f b)
        (q (q.symm (fV (CentralQuotient.projection D h K u))))
  rw [q.apply_symm_apply,←CentralQuotient.representation_mk D h K hn,hfV]

/-- The actual A₈ orders contradict the original source core bound. -/
theorem alternating_eight_source_false
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (f : Catalogue.actor D K ≃* alternatingGroup (Fin 8))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      centralProjection D h fV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (f b)
          (centralProjection D h fV u)) : False := by
  obtain ⟨hc,hi⟩ := alternating_eight_source_orders d h hA312 hH hnot hU K s hLK f fV hfV
  exact source_a8_order_exclusion d hA312 hH hU
    (alternating_eight_source_generation d h hA312 hH hnot hU K s hLK f fV hfV) hc hi

/-- Every natural central quotient of the same original selected component is
excluded by the source chief-count, order, and fixed-point bounds. -/
theorem source_natural_quotient_false
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (hn : (starImage D.H K).Normal)
    (hnat : CentralQuotient.NaturalAction (Catalogue.component D K)
      ((CentralQuotient.representation D h K hn).comp (Catalogue.actor D K).subtype)) :
    False := by
  rcases hnat with ⟨f,fV,_,hfV⟩ | ⟨f,fV,_,hfV⟩ | ⟨f,fV,_,hfV⟩
  · exact symmetric_six_quotient_false d h hA312 hH hU hnot K s hLK hn f fV hfV
  · apply alternating_eight_source_false d h hA312 hH hU hnot K s hLK f fV
    intro b u
    change fV (CentralQuotient.projection D h K
      (Action.starRepresentation D h b.val u)) = _
    rw [←CentralQuotient.representation_mk D h K hn]
    exact hfV b (CentralQuotient.projection D h K u)
  · exact g2_source_false d h hA312 hH hU hnot K s hLK hn f fV hfV
end CFSG.Quasithin.Chapter13.Section05.A5Source

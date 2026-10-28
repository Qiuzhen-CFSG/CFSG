module
public import Theory.Representation.SL2NaturalOffenders.Marked
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.SourceSections

/-!
# The Sylow and parameter conclusions of DGS (7.1)

Once the corrected earlier module theorem has recognized the two literal
center sections as natural, reciprocal fixed-index counting forces each
opposite center to fill a Sylow subgroup in the actual two-core quotient.
Lifting through that quotient gives the source products Zα′Qα and ZαQα′;
their quotient orders identify the two actual field parameters.

The SL₂ isomorphisms and equivariant natural coordinates are explicit
inputs from (5.12) and the local (6.1) identification. They are not proved
by this file. The corrected generation premise for that earlier application
is proved separately in `SourceSections`. The final graph realization and
the distance exclusions remain obligations of the Chapter 7 owner.

Source: DGS, *Groups and Graphs* (1985), (7.1)(a,c), printed pp.126–127.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

/-- Noncommutation makes the actual opposite-center image nontrivial. -/
theorem quotient_actor_ne_bot (L Q Z A : Subgroup G)
    [(Q.subgroupOf L).Normal] (hAL : A ≤ L)
    (hQC : Q ≤ centralizer (Z : Set G)) (hne : ⁅Z,A⁆ ≠ ⊥) :
    (A.subgroupOf L).map (QuotientGroup.mk' (Q.subgroupOf L)) ≠ ⊥ := by
  intro h
  have hker := (Subgroup.map_eq_bot_iff (A.subgroupOf L)).mp h
  rw [QuotientGroup.ker_mk'] at hker
  apply hne
  rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
  intro a ha
  exact hQC (hker (show (⟨a,hAL ha⟩ : L) ∈ A.subgroupOf L from ha))

/-- Lift the quotient Sylow to the literal product with its two-group kernel.
Normality is relative to L, and no finiteness of the ambient completion is used. -/
theorem quotient_sylow_lifts_join (L Q A : Subgroup G)
    [(Q.subgroupOf L).Normal] (hQL : Q ≤ L) (hAL : A ≤ L)
    (hp : IsPGroup 2 Q)
    (hS : ∃ S : Sylow 2 (L ⧸ Q.subgroupOf L),
      (S : Subgroup (L ⧸ Q.subgroupOf L)) =
        (A.subgroupOf L).map (QuotientGroup.mk' (Q.subgroupOf L))) :
    Stellmacher.IsSylowSubgroupIn (A ⊔ Q) L := by
  obtain ⟨S,hS⟩ := hS
  let π := QuotientGroup.mk' (Q.subgroupOf L)
  have hk : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact hp.comap_subtype
  let T := S.comapOfKerIsPGroup π hk (by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact le_top)
  refine ⟨T,?_⟩
  change ((S : Subgroup (L ⧸ Q.subgroupOf L)).comap π).map L.subtype = A ⊔ Q
  rw [hS,comap_map_eq,QuotientGroup.ker_mk',Subgroup.map_sup,
    map_subgroupOf_eq_of_le hAL,map_subgroupOf_eq_of_le hQL]

/-- The lifted source product is the original Sylow when contained in it. -/
theorem sylow_join_eq_of_le (L A Q S : Subgroup G)
    (h : Stellmacher.IsSylowSubgroupIn (A ⊔ Q) L)
    (hp : IsPGroup 2 S) (hSL : S ≤ L) (hAS : A ≤ S) (hQS : Q ≤ S) :
    A ⊔ Q = S := by
  obtain ⟨T,hT⟩ := h
  have he := inf_eq_sylow_map T hp (hT ▸ sup_le hAS hQS)
  rw [inf_of_le_left hSL,hT] at he
  exact he.symm

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open scoped MatrixGroups
variable {G : Type*} [Group G]

/-- The two actual natural sections have equal field orders and opposite
centers supplementing their original cores to Sylow subgroups. The estimate
inputs of `source_core_quotient_reciprocal` are discharged by the marked
natural actions; neither Sylow maximality nor field equality is assumed. -/
theorem source_natural_endpoints
    (P₀ P₁ L₀ L₁ Z₀ Z₁ : Subgroup G) [Finite P₀] [Finite P₁]
    [IsElementaryAbelian 2 Z₀] [IsElementaryAbelian 2 Z₁]
    [((P₀.pCoreIn 2).subgroupOf L₀).Normal]
    [((P₁.pCoreIn 2).subgroupOf L₁).Normal]
    {W₀ W₁ F₀ F₁ : Type*}
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    [Field F₀] [Finite F₀] [CharP F₀ 2] [Algebra (ZMod 2) F₀]
    [Field F₁] [Finite F₁] [CharP F₁ 2] [Algebra (ZMod 2) F₁]
    (σ₀ : Representation (ZMod 2) (L₀ ⧸ (P₀.pCoreIn 2).subgroupOf L₀) W₀)
    (σ₁ : Representation (ZMod 2) (L₁ ⧸ (P₁.pCoreIn 2).subgroupOf L₁) W₁)
    (d₀ : BinaryConjugationSection L₀ Z₀ (Stellmacher.omegaOneCenterAmbient L₀)
      (σ₀.comp (QuotientGroup.mk' ((P₀.pCoreIn 2).subgroupOf L₀))))
    (d₁ : BinaryConjugationSection L₁ Z₁ (Stellmacher.omegaOneCenterAmbient L₁)
      (σ₁.comp (QuotientGroup.mk' ((P₁.pCoreIn 2).subgroupOf L₁))))
    (e₀ : (L₀ ⧸ (P₀.pCoreIn 2).subgroupOf L₀) ≃* SL(2,F₀))
    (e₁ : (L₁ ⧸ (P₁.pCoreIn 2).subgroupOf L₁) ≃* SL(2,F₁))
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → F₀))
    (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → F₁))
    (he₀ : ∀ g w, E₀ (σ₀ g w) = Matrix.mulVec (e₀ g).val (E₀ w))
    (he₁ : ∀ g w, E₁ (σ₁ g w) = Matrix.mulVec (e₁ g).val (E₁ w))
    (hL₀ : L₀ ≤ P₀) (hL₁ : L₁ ≤ P₁)
    (h₁₀ : Z₁ ≤ L₀) (h₀₁ : Z₀ ≤ L₁)
    (hQ₀ : P₀.pCoreIn 2 ≤ L₀) (hQ₁ : P₁.pCoreIn 2 ≤ L₁)
    (hQC₀ : P₀.pCoreIn 2 ≤ centralizer (Z₀ : Set G))
    (hQC₁ : P₁.pCoreIn 2 ≤ centralizer (Z₁ : Set G))
    (hS₀ : Stellmacher.IsSylowSubgroupIn (P₀.pCoreIn 2) (L₀ ⊓ centralizer (Z₀ : Set G)))
    (hS₁ : Stellmacher.IsSylowSubgroupIn (P₁.pCoreIn 2) (L₁ ⊓ centralizer (Z₁ : Set G)))
    (hne : ⁅Z₀,Z₁⁆ ≠ ⊥) :
    Nat.card F₀ = Nat.card F₁ ∧
      Stellmacher.IsSylowSubgroupIn (Z₁ ⊔ P₀.pCoreIn 2) L₀ ∧
      Stellmacher.IsSylowSubgroupIn (Z₀ ⊔ P₁.pCoreIn 2) L₁ ∧
      Nat.card ((Z₁.subgroupOf L₀).map
        (QuotientGroup.mk' ((P₀.pCoreIn 2).subgroupOf L₀))) = Nat.card F₀ ∧
      Nat.card ((Z₀.subgroupOf L₁).map
        (QuotientGroup.mk' ((P₁.pCoreIn 2).subgroupOf L₁))) = Nat.card F₁ := by
  let A₀ := (Z₁.subgroupOf L₀).map (QuotientGroup.mk' ((P₀.pCoreIn 2).subgroupOf L₀))
  let A₁ := (Z₀.subgroupOf L₁).map (QuotientGroup.mk' ((P₁.pCoreIn 2).subgroupOf L₁))
  have hp₀ : IsPGroup 2 A₀ := (IsElementaryAbelian.isPGroup 2 Z₁).comap_subtype.map _
  have hp₁ : IsPGroup 2 A₁ := (IsElementaryAbelian.isPGroup 2 Z₀).comap_subtype.map _
  have hn₀ : A₀ ≠ ⊥ := quotient_actor_ne_bot L₀ _ Z₀ Z₁ h₁₀ hQC₀ hne
  have hn₁ : A₁ ≠ ⊥ := quotient_actor_ne_bot L₁ _ Z₁ Z₀ h₀₁ hQC₁
    (by rwa [commutator_comm])
  have hb₀ := SL2NaturalOffenders.marked_two_subgroup_card_le_fixed_quotient
    e₀ σ₀ E₀ he₀ hn₀ hp₀
  have hb₁ := SL2NaturalOffenders.marked_two_subgroup_card_le_fixed_quotient
    e₁ σ₁ E₁ he₁ hn₁ hp₁
  have hr := source_core_quotient_reciprocal P₀ P₁ L₀ L₁ Z₀ Z₁ σ₀ σ₁ d₀ d₁
    hL₀ hL₁ h₁₀ h₀₁ hQ₀ hQ₁ hQC₀ hQC₁ hS₀ hS₁ hne hb₀ hb₁
  obtain ⟨hc₀,hs₀⟩ := SL2NaturalOffenders.marked_sylow_of_fixed_quotient_le_card
    e₀ σ₀ E₀ he₀ hn₀ hp₀ hr.2.2.2.1.le
  obtain ⟨hc₁,hs₁⟩ := SL2NaturalOffenders.marked_sylow_of_fixed_quotient_le_card
    e₁ σ₁ E₁ he₁ hn₁ hp₁ hr.2.2.2.2.1.le
  exact ⟨hc₀.symm.trans (hr.2.2.1.trans hc₁),
    quotient_sylow_lifts_join L₀ _ Z₁ hQ₀ h₁₀ (isPGroup_pCoreIn 2 P₀) hs₀,
    quotient_sylow_lifts_join L₁ _ Z₀ hQ₁ h₀₁ (isPGroup_pCoreIn 2 P₁) hs₁,hc₀,hc₁⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting

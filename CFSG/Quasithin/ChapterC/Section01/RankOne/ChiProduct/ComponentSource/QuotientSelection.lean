module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.Selection
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.CenterBounds

/-!
# B.1.13 on an actual quotient of an SQTK group

Full A.2 applies to each quasisimple component as an actual section of the
original SQTK cover. The component is therefore SQTK even though the whole
quotient need not be. Its two-core is trivial by subnormal core inheritance,
so A.3.6 supplies its center bound. The faithful section argument now gives
B.1.13 on the literal quotient actor, with its provenance and kernel intact.

Source: Aschbacher--Smith B.1.13, pp.73--74, used on G/C_G(V) in C.1.27.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
open ChapterB Chapter1.Section02 SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
universe u
variable {G V : Type u} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
/-- Only the actual component inherits SQTK from the original cover. -/
theorem component_source_of_sqtk_quotient
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : A36Input.{u} KnownSimple.IsKnownSimple)
    (hq : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple G))
    (hcore : pCore 2 G = ⊥) (L : Subgroup G) (hL : IsComponent G L) :
    IsSQTK KnownSimple.IsKnownSimple L ∧
      (Nat.card (center L) = 1 ∨ Nat.card (center L) = 3) := by
  let : IsQuasisimple L := hL.2
  obtain ⟨c⟩ := hq
  let f : c.Cover →* G := c.equiv.toMonoidHom.comp (QuotientGroup.mk' c.kernel)
  have hf : Function.Surjective f := c.equiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hs : IsSQTK KnownSimple.IsKnownSimple L := quasisimple_section_sqtk hA c.sqtk
    ((ChapterA.Section02.IsSectionOf.subgroup L).ambient_surjective f hf)
  have hLc : pCore 2 L = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hL.1, hcore, MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff L.subtype).mpr L.subtype_injective
  let : IsQuasisimple (⊤ : Subgroup L) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have ht : IsComponent L ⊤ := ⟨(inferInstance : (⊤ : Subgroup L).Normal).isSubnormal, inferInstance⟩
  have hc := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_card_of_common
    (h36 L hs hLc ⊤ ht.isCComponent).2
  have he := Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup L) ≃* L)).toEquiv
  exact ⟨hs, he ▸ hc⟩

/-- The original B.1.13 selection, retaining arbitrary SQTK-quotient
provenance instead of assuming the quotient itself is strongly quasithin. -/
theorem source_selection_of_sqtk_quotient
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hq : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple G))
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (K : Subgroup G) (T : Sylow 2 G)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hcomm : K = ⁅K, generatedBy {A | IsBestOffender ρ A} (T : Subgroup G)⁆) :
    (Nat.card K = 3 ∧ K ≤ (center (fittingSubgroup G)).map (fittingSubgroup G).subtype) ∨
    ∃ L, IsComponent G L ∧ K ≤ L ∧ ⁅L,K⁆ = L ∧
      (K = L ∨ Nonempty (L ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (L ≃* alternatingGroup (Fin 7))) := by
  rcases central_fitting_or_moved_component ρ hf hcore K (T : Subgroup G)
      hkind hK hcomm with hc | ⟨L,hL,hLK⟩
  · exact Or.inl hc
  · obtain ⟨hLsqtk,hc⟩ := component_source_of_sqtk_quotient hA h36 hq hcore L hL
    obtain ⟨hKL,hm⟩ := component_containment_of_source_section ρ K L T hL hLK
      hkind hK hcomm hf hLsqtk hc h4
    exact Or.inr ⟨L,hL,hKL,hLK,hm⟩

/-- Exact selected subnormal container for C.1.27 on its literal quotient
actor. Universal A/C discharge A.2/A.3.6; B.4.2 is the sole earlier module
classification input. -/
theorem exists_subnormal_container_of_sqtk_quotient
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hq : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple G))
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (K : Subgroup G) (T : Sylow 2 G)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hcomm : K = ⁅K, generatedBy {A | IsBestOffender ρ A} (T : Subgroup G)⁆) :
    ∃ B : Subgroup G, B.IsSubnormal ∧ K ≤ B ∧
      (IsQuasisimple B ∨ Nat.card B = 3) ∧ (K = B ∨ ⁅K,B⁆ = B) ∧
      (K = B ∨ Nonempty (B ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (B ≃* alternatingGroup (Fin 7))) := by
  rcases source_selection_of_sqtk_quotient ρ hA
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC) h4 hq hf hcore K T
      hkind hK hcomm with hz | hL
  · exact ⟨K, subnormal_of_le_fitting_center K hz.2, le_rfl, Or.inr hz.1, Or.inl rfl, Or.inl rfl⟩
  · obtain ⟨L,hL,hKL,hLK,hm⟩ := hL
    exact ⟨L,hL.1,hKL,Or.inl hL.2,Or.inr ((commutator_comm K L).trans hLK),hm⟩

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource

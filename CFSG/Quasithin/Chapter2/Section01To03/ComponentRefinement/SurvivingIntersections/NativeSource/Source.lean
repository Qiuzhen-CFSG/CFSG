module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.NativeSourceAssembly
public import CFSG.Quasithin.Chapter1.SourceInputs

/-!
# The original source application of component refinement

The selected Γ₀ configuration constructs every original 1.1.5 hypothesis.
We transport its marked automorphism, fixed Sylow, characteristic-two fixed
subgroup and odd-core inversion along the literal component inclusion. The
full universal A/B/C input then classifies the original ambient component.
The complete intersection assembly leaves precisely the binary M₂₂ cover.

The only earlier source inputs are universal A/B/C and local C.1.29; the
structural 1.1.5 input and all model-specific intersection calculations are
proved. Source: Aschbacher--Smith 2.3.9(7), printed pp.525--526.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory ClassificationModels
open Chapter15.Section03.Candidates.ComponentStructure
open Chapter1.QuasisimpleInvolutions ChapterA.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {C : GroupClass.{u}}
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem marked_transport {A B : Type u} [Group A] [Group B] [Finite A]
    (e : A ≃* B) {α : MulAut A} {P : Sylow 2 A} (d : MarkedInvolution α P) :
    MarkedInvolution ((MulAut.congr e) α) (P.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  refine ⟨?_,?_,d.characteristic_two.of_equiv (MulAut.fixedSubgroupCongr e α),?_⟩
  · exact ((MulAut.congr e).orderOf_eq α).trans d.order_two
  · rintro _ ⟨x,hx,rfl⟩
    change e (α (e.symm (e x))) = e x
    rw [e.symm_apply_apply,d.fixes x hx]
  · intro x hx
    rw [← pPrimeCore_map_iso 2 e] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    change e (α (e.symm (e y))) = (e y)⁻¹
    rw [e.symm_apply_apply,d.inverts_odd_core y hy,map_inv]

/-- Every source premise of 1.1.5 is constructed for the original selected z. -/
theorem MathieuSourceSetup.lemma115_hypotheses
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G) :
    Chapter1.Lemma115Hypotheses H S M z := by
  have hcentral : ∀ s ∈ (S : Subgroup H).map H.subtype, s * z = z * s := by
    intro s hs
    obtain ⟨a,ha,he⟩ := c.mem_center
    rw [← he]
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨s,c.sylow_lt.le hs⟩)
  have hMc : ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M).map M.subtype, x * z = z * x := by
    refine ⟨c.T.subtype c.sylow_le,?_⟩
    intro x hx
    have hxT : x ∈ (c.T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le c.sylow_le] using hx
    obtain ⟨a,ha,he⟩ := c.mem_center
    rw [← he]
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨x,hxT⟩)
  exact lemma_2_3_8_6 hG c.T c.maximal c.sylow_le c.unique c.gamma c.pair S c.base_le
    c.involution (c.center_le c.mem_center) hcentral hMc

/-- Supply the full original model/action alternative on L itself. This
uses the universal A/B/C theorem on actual subgroups and central quotients. -/
theorem MathieuSourceSetup.modelAction115
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC C X) :
    ∃ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧ ModelAction115 L α := by
  let h := c.lemma115_hypotheses hG
  let D := L.subgroupOf H
  let e : D ≃* L := subgroupOfEquivOfLe c.component_le
  obtain ⟨_,α,P,hα,d,_⟩ := h.component_inputs D c.component
  let : IsQuasisimple D := c.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e
  let β := (MulAut.congr e) α
  have db : MarkedInvolution β (P.mapSurjective (f := e.toMonoidHom) e.surjective) := marked_transport e d
  have hnorm : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 H).le_normalizer_map H.subtype
  have hsq := hG.twoLocal_sqtk
    (show IsTwoLocal (normalizer (H.pCoreIn 2 : Set G)) from
      ⟨H.pCoreIn 2,h.mem_H,isPGroup_pCoreIn 2 H,rfl⟩)
  have hln := c.component_le.trans hnorm
  have hl : IsSQTK C L :=
    ⟨hsq.stronglyQuasithin.of_injective (inclusion hln) (inclusion_injective hln),
      hsq.isKGroup.of_injective (inclusion hln) (inclusion_injective hln)⟩
  refine ⟨β,?_,db.classify (quotient_model hl (hABC L).1 (hABC (L ⧸ center L)).2.2)⟩
  intro x
  exact hα (e.symm x)

/-- Full source refinement except for the explicitly retained binary M₂₂
cover. All six source model families and their actual intersections are assembled. -/
theorem MathieuSourceSetup.source_refinement_or_binary_mathieu
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC C X)
    (sourceC : LocalC129Input C G) :
    ((∃ t : L, IsConjugationProjection L z t) ∨
      Nonempty ((L ⧸ center L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ center L) ≃* alternatingGroup (Fin 7))) ∧
    (RefinedIntersection L M ((S : Subgroup H).map H.subtype) z ∨
      (Nat.card (pCore 2 L) = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22) ∧
        IsCyclic (center (c.T : Subgroup G)))) := by
  obtain ⟨α,hα,hm⟩ := c.modelAction115 hG hABC
  have h := c.localSetup hG structural115Input sourceC
  constructor
  · rcases inner_or_alternating_quotient_of_modelAction hm with ⟨t,rfl⟩ | h | h
    · exact .inl ⟨t,fun x => (hα x).symm⟩
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rcases h.refinement_or_binary_mathieu α hα hm with hi | ⟨hk,⟨e⟩⟩
    · exact .inl hi
    · exact .inr ⟨hk,⟨e⟩,c.mathieuTwentyTwo_ambient_center_isCyclic hG sourceC e⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement

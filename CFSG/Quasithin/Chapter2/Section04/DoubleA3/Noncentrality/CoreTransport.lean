module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.MarkedModel
public import Theory.SpecificGroups.PSL3Two.PairedSylowRecognition.FactorCentralizer

/-!
# Transporting the paired model to the original component centralizer

The normal two-core of the component centralizer lies in its original Sylow
subgroup. Under the marked paired equivalence it centralizes the first full
factor, hence embeds in the opposite D₈ factor. The literal 1.1.5 hypotheses
therefore bound the second centralizer's three-rank. Together with the two
characteristic-two nonfusion arguments, the checked five-class transfer
gives a contradiction, without any extra ambient fusion assumptions.

Source: Aschbacher--Smith, proof of Lemma 2.4.34, printed p.548.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.PairedInvolutiveExtension
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.PairedGraphInputs Matrix.PSL3Two.PairedSylowRecognition
namespace CFSG.Quasithin.Chapter2.DoubleA3.SourcePairedEmbedding
variable {G : Type*} [Group G] [Finite G]
variable {M : Subgroup G} {d : MinimalBlockSetup M} {T : Sylow 2 G}
variable {c : SourcePairCoordinates d T} {g : SourceCentralizerGeometry c}
variable {K : Subgroup (involutionCentralizer g.z₂)} (m : SourcePairedEmbedding g K)
include m

omit [Finite G] in
/-- The normal two-core of the original component centralizer embeds in
its literal opposite dihedral Sylow factor. -/
theorem exists_core_embedding [K.Normal] :
    ∃ f : pCore 2 (centralizer (K : Set (involutionCentralizer g.z₂))) →* DihedralGroup 4,
      Function.Injective f := by
  let H := involutionCentralizer g.z₂
  let C : Subgroup H := centralizer (K : Set H)
  let Q : Subgroup C := pCore 2 C
  have hQT : ∀ q : Q, (((q : C) : H) : G) ∈ (T : Subgroup G) := by
    intro q
    have hP : (Q.map C.subtype) ≤ (g.P₂ : Subgroup H) :=
      (show IsPGroup 2 (Q.map C.subtype) from pCore_isPGroup.map C.subtype).le_sylow_of_normal g.P₂
    have hq : ((q : C) : H) ∈ (g.P₂ : Subgroup H) := hP ⟨q, q.property, rfl⟩
    have hm : (((q : C) : H) : G) ∈ (g.P₂ : Subgroup H).map H.subtype := ⟨_, hq, rfl⟩
    rw [g.second_intersection] at hm
    exact hm.1
  let qT : Q →* T :=
    { toFun q := ⟨q.val.val.val,hQT q⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ψ : Q →* standardPaired := m.sylowEquiv.symm.toMonoidHom.comp qT
  have hψ (q : Q) : m.f (ψ q : StandardModel) = (((q : C) : H) : G) := by
    rw [m.sylow_spec]
    exact congrArg Subtype.val (m.sylowEquiv.apply_symm_apply (qT q))
  let φ : Q →* firstFactorCentralizer :=
    { toFun q := ⟨ψ q, by
        constructor
        · apply mem_centralizer_iff.mpr
          rintro _ ⟨a,rfl⟩
          apply m.injective
          rw [map_mul,map_mul,hψ,m.first_eval]
          exact congrArg Subtype.val (mem_centralizer_iff.mp q.val.property
            (m.componentEquiv.symm a) (m.componentEquiv.symm a).property)
        · exact (ψ q).property⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg (fun u : standardPaired => (u : StandardModel)) ψ.map_one
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact congrArg (fun u : standardPaired => (u : StandardModel)) (ψ.map_mul a b) }
  have hφ : Function.Injective φ := by
    intro a b hab
    have hψeq : ψ a = ψ b := Subtype.ext (congrArg (fun u : firstFactorCentralizer => (u : StandardModel)) hab)
    have ht : qT a = qT b := m.sylowEquiv.symm.injective hψeq
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : T => (u : G)) ht
  exact ⟨firstFactorCentralizerEquivDihedral.toMonoidHom.comp φ,
    firstFactorCentralizerEquivDihedral.injective.comp hφ⟩

/-- The actual source centralizers and marked paired model yield the
contradiction of 2.4.34, with no ambient fusion premises left. -/
theorem false_of_source [K.Normal]
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) : False := by
  obtain ⟨f,hf⟩ := m.exists_core_embedding
  have hxa := source_actor_not_conj_product g h K
    (m.f (graph diagram diagram_involutive)) m.graph_mem_second m.componentFixedEquiv
  have hxb := source_actor_not_conj_second g h K m.first_mem
    (m.componentEquiv.trans Matrix.PSL3Two.equiv) f hf
    (m.f (graph diagram diagram_involutive)) m.graph_three_rank
  have hba := source_second_not_conj_product g h K hK
  apply Matrix.PSL3Two.PairedInvolutionGeometry.ambient_transfer_false T hno
    diagram diagram_involutive diagram_ne_conj borelSL diagram_stable_borel card_borelSL
    highestRoot highestRoot_mem_borel highestRoot_orderOf diagram_highestRoot
    m.f m.sylowEquiv m.sylow_spec
  · simpa only [m.product_mark] using hxa
  · simpa only [m.second_mark] using hxb
  · simpa only [m.product_mark,m.second_mark] using hba

end CFSG.Quasithin.Chapter2.DoubleA3.SourcePairedEmbedding

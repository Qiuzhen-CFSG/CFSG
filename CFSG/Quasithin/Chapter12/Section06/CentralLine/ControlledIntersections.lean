module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalCoreBound
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.CoreMarking

/-!
# Original fixed-space intersections after nonsingular centralizer control

Normalizer uniqueness controls every nonidentity original L-fixed vector.
The proved nontrivial-fixed-space branch of 12.6.2 controls every nonsingular
vector. Thus, once the source fusion assertion is supplied, every nonidentity
intersection vector outside N_G(V) has weight four in the original compatible
augmentation-core marking. The intersection rank is at most three and the
literal r(G,V) is at least four.

These results discharge the centralizer premises in the actual 12.6.20
consumer. Fusion (12.6.19), the weak-closure calculation and the local H*
construction remain required for 12.6.23. Earlier invariance/TI retain
qt-d-1222-source and final discharge retains qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.19--20, printed pp.828--829.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open CentralLine
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Uniqueness controls the full centralizer of every nonidentity original
fixed vector, rather than merely its intersection with a local subgroup. -/
theorem SourceHypothesis.fixed_vector_centralizer_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (z : G) (hz : z ∈ ZV L V) (hne : z ≠ 1) : Gv z ≤ M L := by
  have hline : zpowers z ≤ ZV L V := zpowers_le.mpr hz
  have hnon : zpowers z ≠ ⊥ := fun h => hne (by
    have hh := mem_zpowers z
    rwa [h,mem_bot] at hh)
  have hn : normalizer (zpowers z : Set G) ≤ M L :=
    H.chosen.normal_subgroup_normalizer_le H.source.toHypothesis1221
      (hline.trans (inf_le_left.trans (H.chosen.le_component.trans le_sup_left))) hnon
      (((D.join_centralizes_fixed H.chosen hTV).trans (centralizer_le hline)).trans
        (Subgroup.centralizer_le_normalizer _))
  intro g hg
  apply hn
  rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
  exact congrArg zpowers (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg))

/-- The full source intersection statement retains weight four and the
actual marking commuting with the original fixed-space projection. -/
theorem SourceHypothesis.fixed_core_weight_four_intersections_of_fusion
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : HasTIConjugatesIn V (M L))
    (hz : ZV L V ≠ ⊥) (hf : ControlsElementFusion L V) :
    ∃ E : Additive V ≃ₗ[ZMod 2] core (Fin 8),
      (∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) ∧
      (∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w)) ∧
      (∀ g ∉ normalizer (V : Set G),
        (∀ x ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom,
          x ≠ 1 → x ∈ markedVectors E coreWeightFour) ∧
        Nat.log 2 (Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) ≤ 3) ∧
      4 ≤ ChapterE.globalR V := by
  obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  have hbound (X : Submodule (ZMod 2) (core (Fin 8)))
      (hX : ∀ x ∈ X, x ≠ 0 → coreWeightFour x) : Module.finrank (ZMod 2) X ≤ 3 := by
    apply EightGeometry.finrank_weight_four_le X
    intro x hx hn
    simpa only [coreWeightFour,Fintype.card_subtype,hammingNorm] using hX x hx hn
  have hC : ∀ x ∈ V, x ≠ 1 → x ∉ markedVectors E coreWeightFour →
      centralizer ({x} : Set G) ≤ M L := by
    intro x hx hx1 hnot
    let w : Additive V := Additive.ofMul ⟨x,hx⟩
    by_cases hzero : (Submodule.Quotient.mk w : Vhat L V H.chosen.normalizes) = 0
    · exact H.fixed_vector_centralizer_le D hTV x
        ((mem_fixedSeed_iff L V H.chosen.normalizes w).mp
          ((Submodule.Quotient.mk_eq_zero _).mp hzero)) hx1
    · apply H.nonsingular_centralizer_le_of_fixed D hTV hTI hz ⟨x,hx⟩
      intro hs
      have hq : coreToNatural (Fin 8) (E w) ≠ 0 := by
        rw [hproj]
        exact fun hh => hzero (D.coordinates.injective (hh.trans D.coordinates.map_zero.symm))
      have hw : hammingNorm (E w).val = 4 :=
        (EightGeometry.nonzero_singular_core_iff (E w)).mp
          ⟨hq,by rw [hproj]; exact hs⟩
      apply hnot
      refine ⟨hx,?_⟩
      simpa only [coreWeightFour,Fintype.card_subtype,hammingNorm] using hw
  exact ⟨E,hE,hproj,core_intersections_and_globalR E hbound H.chosen.normalizes hf hTI hC⟩

/-- Source 12.6.20(1,3) for nontrivial original fixed space, with both
centralizer premises discharged. The source fusion assertion remains explicit. -/
theorem SourceHypothesis.fixed_core_intersections_of_fusion
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hz : ZV L V ≠ ⊥) (hf : CentralLine.ControlsElementFusion L V) :
    (∀ g ∉ normalizer (V : Set G),
      Nat.log 2 (Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) ≤ 3) ∧
      4 ≤ ChapterE.globalR V := by
  obtain ⟨_,_,_,hi,hr⟩ := H.fixed_core_weight_four_intersections_of_fusion D hTV hTI hz hf
  exact ⟨fun g hg => (hi g hg).2,hr⟩

end CFSG.Quasithin.Chapter12.Section06

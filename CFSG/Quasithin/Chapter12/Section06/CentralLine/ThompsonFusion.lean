module
public import Theory.GroupTheory.ElementaryThompsonFusion
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.ControlledIntersections
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FixedFreeFusion

/-!
# Fusion when the original Thompson subgroup centralizes V

Under J(T) <= Q, Thompson heredity and original normalizer uniqueness
put N_G(J(T)) in M. Since J(T) centralizes V, Burnside fusion supplies an
M-conjugator. The original TI property makes it normalize V, and the
actual orbit-preservation theorem replaces it by an element of L.

Every point centralizer also has a Sylow in M: choose it to contain J(T),
then apply weak closure of the elementary Thompson subgroup. Thus the
literal relative index |C_G(v):C_M(v)| is odd for every original v in V.
These prove both clauses of 12.6.19 in this branch. The correcting
conjugator and the compatible seven-dimensional intersection marking
apply them to 12.6.20, giving weight four, rank at most three and r(G,V)>=4.

Combining this branch with fixed-free fusion forces any remaining fusion
failure into C_V(L) nontrivial and J(T) not contained in Q. Original
Thompson generation then makes L centralize the original central omega;
at each of its nonidentity points the canonical residual is exactly L.

Fusion in that remaining branch, HS/J4 exclusion, weak closure and final
fixed-space elimination remain required. Neither full 12.6.2 nor 12.6.23
is asserted. Earlier invariance/TI retain qt-d-1222-source and final
source discharge retains qt-d-12634-source.

Source: Aschbacher--Smith, 12.6.1(5--6), 12.6.19--20 and A.1.35,
combined manuscript of 1 March 2004, printed pp.823,828--829 and 30.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open CentralLine
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [IsElementaryAbelian 2 V] in
/-- Original normalizer uniqueness controls N_G(J(T)) in the small Thompson branch. -/
theorem SourceHypothesis.thompson_normalizer_le_of_le_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M L := by
  rw [(thompson_eq_of_le_core H.chosen (1 : V) hJ).1]
  exact H.core_thompson_normalizer

/-- Source 12.6.19(1) when J(T) <= Q, including nontrivial original fixed space. -/
theorem SourceHypothesis.controls_element_fusion_of_thompson_le_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTI : HasTIConjugatesIn V (M L))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L) :
    ControlsElementFusion L V := by
  intro x hx g hg
  by_cases hx1 : x = 1
  · subst x
    exact ⟨1,L.one_mem,by simp⟩
  have hVC : V ≤ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (hJ.trans H.chosen.core_centralizes)
  obtain ⟨n,hn,he⟩ := maxJ_controls_centralizer_fusion T (hVC hx) (hVC hg)
    (isConj_iff.mpr ⟨g,rfl⟩)
  have hnM := H.thompson_normalizer_le_of_le_core hJ hn
  have hnV : n ∈ normalizer (V : Set G) := by
    rcases hTI n hnM with hi | hi
    · have hnon : MulAut.conj g x ≠ 1 := fun h => hx1
        ((MulAut.conj g).injective (h.trans (MulAut.conj g).map_one.symm))
      have hm : MulAut.conj g x ∈ V ⊓ V.map (MulAut.conj n).toMonoidHom :=
        ⟨hg,x,hx,he⟩
      exact (hnon (mem_bot.mp (hi ▸ hm))).elim
    · exact mem_normalizer_iff_map_conj_eq.mpr hi
  obtain ⟨l,hl⟩ := D.normalizer_orbit_control H.chosen n hnM hnV ⟨x,hx⟩
  exact ⟨l,l.property,hl.symm.trans he⟩

omit [IsElementaryAbelian 2 V] in
/-- Source 12.6.19(2) in the small Thompson branch, for every original vector. -/
theorem SourceHypothesis.centralizer_odd_index_of_thompson_le_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L) (v : V) :
    Odd ((Mv L (v : G)).relIndex (Gv (v : G))) := by
  exact odd_centralizer_index_of_maxJ_normalizer_le T (M L)
    (H.thompson_normalizer_le_of_le_core hJ) (v : G)
    ((le_centralizer_iff.mp (hJ.trans H.chosen.core_centralizes)) v.property)

/-- The literal correcting conjugator of 12.6.20(2), with fusion discharged. -/
theorem SourceHypothesis.centralizer_conjugator_of_thompson_le_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTI : HasTIConjugatesIn V (M L))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L)
    {v g : G} (hv : v ∈ V) (hvg : v ∈ V.map (MulAut.conj g).toMonoidHom) :
    ∃ c : centralizer ({v} : Set G),
      V.map (MulAut.conj (c : G)).toMonoidHom = V.map (MulAut.conj g).toMonoidHom :=
  centralizer_conjugator H.chosen.normalizes
    (H.controls_element_fusion_of_thompson_le_core D hTI hJ) hv hvg

/-- The original marked intersection conclusion, with fusion and centralizer premises discharged in this branch. -/
theorem SourceHypothesis.fixed_core_intersections_of_thompson_le_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L) :
    ∃ E : Additive V ≃ₗ[ZMod 2] core (Fin 8),
      (∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) ∧
      (∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w)) ∧
      (∀ g ∉ normalizer (V : Set G),
        (∀ x ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom,
          x ≠ 1 → x ∈ markedVectors E coreWeightFour) ∧
        Nat.log 2 (Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) ≤ 3) ∧
      4 ≤ ChapterE.globalR V :=
  H.fixed_core_weight_four_intersections_of_fusion D hTV hTI hz
    (H.controls_element_fusion_of_thompson_le_core D hTI hJ)

/-- Every remaining fusion failure forces original Thompson generation and central-omega residual L. -/
theorem SourceHypothesis.fusion_failure_forces_central_omega
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : HasTIConjugatesIn V (M L)) (hf : ¬ ControlsElementFusion L V) :
    ZV L V ≠ ⊥ ∧ ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      L ≤ centralizer (Z T : Set G) ∧
      ∀ z ∈ Z T, z ≠ 1 → Gv z ≤ M L ∧ Kv z = L := by
  have hz : ZV L V ≠ ⊥ := fun h => hf (H.fixed_free_controls_element_fusion D hTV hTI h)
  have hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L :=
    fun h => hf (H.controls_element_fusion_of_thompson_le_core D hTI h)
  have hgen := H.eq_commutator_thompson_of_not_le_core hj
  have hLZ := H.component_centralizes_Z_of_thompson_generation D hz hgen
  refine ⟨hz,hj,hgen,hLZ,?_⟩
  intro z hz hne
  have hc := H.central_omega_point_control hLZ z hz hne
  refine ⟨hc,H.Kv_eq_of_centralizer_bounds D z ?_ hc⟩
  intro l hl
  exact mem_centralizer_singleton_iff.mpr ((hLZ hl z hz).symm)
end CFSG.Quasithin.Chapter12.Section06

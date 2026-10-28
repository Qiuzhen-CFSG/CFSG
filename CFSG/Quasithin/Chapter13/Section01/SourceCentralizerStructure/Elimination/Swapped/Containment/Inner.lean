module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Containment.Factors
public import CFSG.Quasithin.Chapter1.Section03.Basic.TwoOrbitFrattini
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceSwapped

/-!
# Containment in the actual exchanged centralizer orbit

The odd Sylow image acts irreducibly on its Frattini quotient and nontrivially
on the component modulo the centralizer's two-core. The genuine SQTK component
classification supplies an index-two normalizer and abelian or two-group outer
automorphisms. Thus the image acts inner on the orbit. The rank-two containment
lemma puts it in that orbit; coprime lifting and two-perfectness then put the
whole canonical radical in the original T_u-orbit.

Source: Aschbacher--Smith, 13.1.12(3), printed p.874. The subsequent Rows module supplies
the model parameter restrictions and assembles the complete swapped sieve.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K : Subgroup G} {p : ℕ} [Fact p.Prime] {u : G}

theorem Context.swapped_quotient_containment (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L)) :
    quotientImage (centralizer ({u} : Set G))
        ((P : Subgroup (XiP p L)).map (XiP p L).subtype) ≤
      quotientImage (centralizer ({u} : Set G))
        (componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G))) := by
  let H := centralizer ({u} : Set G)
  let S := (T : Subgroup G) ⊓ H
  let D := componentOrbit K S
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  let B := quotientImage H K
  let A := quotientImage H S
  have hPH : P₀ ≤ H := (map_subtype_le _).trans
    ((SourceNonquasisimple.XiP_le_moved_centralizer h.hypothesis h.many h.maximal.1
      h.nonquasisimple p s.mem).trans inf_le_right)
  let ek := subgroupOfEquivOfLe e.component.1
  let eqk : XiQuotient (K.subgroupOf H) ≃* XiQuotient K :=
    QuotientGroup.congr _ _ ek (pCore_map_iso 2 ek)
  let hq : IsQuasisimple (XiQuotient (K.subgroupOf H)) := e.quotient.of_mulEquiv eqk.symm
  have hB : IsComponent (XiQuotient H) B :=
    ⟨e.component.2.subnormal.map (QuotientGroup.mk'_surjective _),
      IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv e.component.2)⟩
  have hd : ComponentDetection P₀ H K :=
    ⟨e.component,e.quotient,hB,h.odd_sylow_noncentral s e P⟩
  have hn : ¬ B.Normal := hd.quotient_not_normal_of_not_normal
    (h.component_not_normal_of_reducible o s e hr)
  have hH := h.hypothesis.simpleQTKE.involution_centralizer_sqtk
    (h.involution s.mem s.ne_one)
  have hsq : IsSQTK KnownSimple.IsKnownSimple (XiQuotient H) :=
    ⟨quotient_stronglyQuasithin hH.stronglyQuasithin,hH.isKGroup.quotient _⟩
  have hi : (normalizer (B : Set (XiQuotient H))).index = 2 :=
    (component_normal_or_index_two_source hsq (component_isCComponent hB)).resolve_left hn
  have hout := ChapterA.SQTKStructure.NonnormalOuterSource.nonnormal_component_outer
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hsq (pCore_quotient_pCore_eq_bot 2) B hB hn
  let : (D.subgroupOf H).Normal := e.orbit_normal hH
  let : (quotientImage H D).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have he := quotientImage_componentOrbit_source H K S e.component.1
    (show S ≤ H from inf_le_right)
  let : (componentOrbit B A).Normal := he ▸ (inferInstance : (quotientImage H D).Normal)
  obtain ⟨hshape,hirr⟩ := h.swapped_quotient_complement o s P
  have hinner : quotientImage H P₀ ≤ quotientImage H D ⊔
      centralizer (quotientImage H D : Set (XiQuotient H)) := by
    rw [he]
    exact hirr.inner_on_two_component_orbit B _ A hshape.isPGroup h.odd
      hshape.not_isCyclic hB hi hout
  let : Group.IsPerfect (quotientImage H D) := by
    rw [he]
    exact hB.orbit_isPerfect A
  apply hirr.le_normal_of_inner_of_exponent_p hshape.isPGroup h.odd
    hshape.not_isCyclic ?_
    (quotient_stronglyQuasithin hH.stronglyQuasithin p (Fact.out : p.Prime) h.odd)
    _ hinner ?_
  · intro a
    rcases hshape with ⟨he,_⟩ | ⟨_,_,hexp⟩
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.exponent_dvd_p a
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (dvd_of_eq hexp) a
  · intro hz
    apply hd.quotient_commutator_ne_bot hPH
    exact bot_unique ((commutator_mono
      (map_mono (subgroupOf_mono H (le_componentOrbit K S))) le_rfl).trans_eq hz)

/-- The full radical lies in the orbit of K under the literal point Sylow. -/
theorem Context.swapped_containment (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) :
    XiP p L ≤ componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) := by
  let P : Sylow p (XiP p L) := Classical.choice inferInstance
  exact h.swapped_containment_of_quotient s e P (h.swapped_quotient_containment o s e hr P)

/-- All complement geometry is constructed; the remaining input is precisely
one of the four source rows with its numerical restrictions. -/
theorem Context.swapped_data_of_row (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L))
    (hrow : SwappedRow p (XiQuotient K)) :
    SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) :=
  h.swapped_data_of_quotient_row o s e hr P (h.swapped_quotient_containment o s e hr P) hrow

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination

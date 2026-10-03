module

public import Stellmacher.PushingUp.CriticalClosureContainment
public import Stellmacher.PushingUp.ShiftClosureNormal
public import Stellmacher.PushingUp.ShiftCoreIntersectionNormal
public import Stellmacher.PushingUp.ShiftCoreIntersectionNormalLeft
public import Stellmacher.PushingUp.ShiftCoreIntersectionObstruction

/-!
# The critical distance is zero, two, or four

This module proves Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (2.4),
for the finite-group amalgam used in the proof of theorem 2. Under condition
(P), nontriviality of the Sylow 2-subgroup, and the prescribed `SL₂(2)`
Frattini quotient, the critical distance is zero, two, or four.

Evenness reduces the contrary case to distance at least six. The attained
minimum and a shortest path give the exact frame for the distance-two shift.
A conjugate of the shifted endpoint center generates the shifted stabilizer
modulo its core. The critical-closure containment theorem then supplies source
step (2); the normality leaves give the closure and the shared core normal
in the shifted stabilizer. Their commutator is central on the original left
stabilizer. Its normal centralizer in the shifted stabilizer contains the
common Sylow subgroup and its chosen conjugate, so it is central there too.
The normal-closure argument makes the shared core normal on the original
left, contradicting the orbit obstruction. These are source steps (3), (4),
and the final paragraph, assembled from the checked leaves.

The vertex set and the free amalgam may be infinite. Finite local stabilizers,
the public attained-minimum API, and shortest walks suffice throughout.
-/

namespace Stellmacher.PushingUp
open scoped commutatorElement
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

private theorem criticalDistance_even_and_six_le_of_not_small [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hnot : ¬ (criticalDistance S = 0 ∨ criticalDistance S = 2 ∨
      criticalDistance S = 4)) :
    Even (criticalDistance S) ∧ 6 ≤ criticalDistance S := by
  have heven : Even (criticalDistance S) :=
    (criticalDistance_basic S T hTS hP hSne
      (mVertex S 1) (hVertex S 1) ⟨1, by simp⟩ (base_adjacent S))
      |>.criticalDistance_even
  constructor
  · exact heven
  · rcases heven with ⟨k, hk⟩
    omega

private theorem exists_distanceTwoShift_frame_of_criticalPair [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (hcrit : IsCriticalPair S a a')
    (hge : 6 ≤ criticalDistance S) :
    ∃ aPrimeMinusTwo : Vertex S,
      DistanceTwoShift.Frame S a a' aPrimeMinusTwo := by
  obtain ⟨p, hp⟩ :=
    (cosetGraph_connected S).exists_walk_length_eq_dist a a'
  have hpLen : p.length = criticalDistance S := hp.trans hcrit.2.1
  let aPrimeMinusTwo := p.getVert (criticalDistance S - 2)
  have htake : (p.take (criticalDistance S - 2)).length =
      (cosetGraph S).dist a aPrimeMinusTwo := by
    simpa [aPrimeMinusTwo] using
      (SimpleGraph.length_eq_dist_of_subwalk hp
        (p.isSubwalk_take (criticalDistance S - 2)))
  have hdrop : (p.drop (criticalDistance S - 2)).length =
      (cosetGraph S).dist aPrimeMinusTwo a' := by
    simpa [aPrimeMinusTwo] using
      (SimpleGraph.length_eq_dist_of_subwalk hp
        (p.isSubwalk_drop (criticalDistance S - 2)))
  refine ⟨aPrimeMinusTwo, ⟨?_, ?_⟩⟩
  · rw [← htake]
    simp only [SimpleGraph.Walk.take_length, hpLen]
    omega
  · rw [← hdrop]
    simp only [SimpleGraph.Walk.drop_length, hpLen]
    omega

private def CriticalDistanceBound.InitialData [Finite M]
    (S : Subgroup M) : Prop :=
  ∃ a a' aPrimeMinusTwo aMinusTwo : Vertex S,
    6 ≤ criticalDistance S ∧
      IsCriticalPair S a a' ∧
      DistanceTwoShift.Frame S a a' aPrimeMinusTwo ∧
      DistanceTwoShift.Conclusion S a a' aPrimeMinusTwo aMinusTwo

private theorem criticalDistanceBound_initialData [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (hnot : ¬ (criticalDistance S = 0 ∨ criticalDistance S = 2 ∨
      criticalDistance S = 4)) :
    CriticalDistanceBound.InitialData S := by
  have hge :=
    (criticalDistance_even_and_six_le_of_not_small S T hTS hP hSne hnot).2
  let a : Vertex S := mVertex S 1
  have ha : InMVertexOrbit S a := ⟨1, by simp [a]⟩
  obtain ⟨a', hcrit⟩ := criticalPair_exists S T hTS hP hSne a ha
  obtain ⟨aPrimeMinusTwo, hframe⟩ :=
    exists_distanceTwoShift_frame_of_criticalPair S a a' hcrit hge
  obtain ⟨aMinusTwo, hshift⟩ :=
    criticalPair_distanceTwoShift S T hTS hP hSne hA a a'
      hcrit (by omega) aPrimeMinusTwo hframe
  exact ⟨a, a', aPrimeMinusTwo, aMinusTwo, hge, hcrit, hframe, hshift⟩

private theorem criticalPair_exists_generating_conjugator [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (u c : Vertex S) (hcrit : IsCriticalPair S u c)
    (hb : 0 < criticalDistance S) :
    ∃ t : FreeAmalgam S, t ∈ stabilizer S u ∧
      vertexZ S c ⊔ (vertexZ S c).map (MulAut.conj t⁻¹).toMonoidHom ⊔
        vertexTwoCore S u = stabilizer S u := by
  obtain ⟨hV, hc, hSL2⟩ := criticalPair_sl2Two S T hTS hP hSne hA u c hcrit hb
  obtain ⟨R, hR⟩ := hSL2.sourceSylow
  let A : Subgroup (stabilizer S u) := (vertexZ S c).subgroupOf (stabilizer S u)
  have hAR : A ⊔ pCore 2 (stabilizer S u) = (R : Subgroup (stabilizer S u)) := by
    apply Subgroup.map_injective (stabilizer S u).subtype_injective
    rw [Subgroup.map_sup]
    rw [Subgroup.map_subgroupOf_eq_of_le hc]
    simpa only [vertexTwoCore, twoCoreAmbient, sylowAt] using hR.symm
  have hNested := stabilizer_isSL2Two_nested_of_mOrbit S u hcrit.1 hA
  obtain ⟨g, hg⟩ := SectionTwo.exists_conjugate_sup_core_eq_top_of_nestedSL2Two
    A R hAR hNested
  refine ⟨(g : FreeAmalgam S)⁻¹, (stabilizer S u).inv_mem g.property, ?_⟩
  have hmap := congrArg (Subgroup.map (stabilizer S u).subtype) hg
  rw [Subgroup.map_sup, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hc] at hmap
  have hconj : (A.conjBy g).map (stabilizer S u).subtype =
      (vertexZ S c).map (MulAut.conj (g : FreeAmalgam S)).toMonoidHom := by
    rw [Subgroup.conjBy, Subgroup.map_map]
    have hcomp : (stabilizer S u).subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : FreeAmalgam S)).toMonoidHom.comp (stabilizer S u).subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hc]
  rw [hconj] at hmap
  simpa only [inv_inv, vertexTwoCore, twoCoreAmbient, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] using hmap
private theorem assembly_mapped_center_le_centralizer {H : Type*} [Group H]
    (G : Subgroup H) :
    (Subgroup.center G).map G.subtype ≤ Subgroup.centralizer (G : Set H) := by
  rintro r ⟨rG, hrG, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hrG) ⟨g, hg⟩)

private theorem central_of_normal_of_conjugate_generation
    {G : Type*} [Group G] (Y E A : Subgroup G) [Y.Normal]
    (t : G) (hAE : A ≤ E)
    (hgen : E ⊔ A.map (MulAut.conj t).toMonoidHom = ⊤)
    (hEY : E ≤ Subgroup.centralizer (Y : Set G)) :
    Y ≤ Subgroup.center G := by
  apply Subgroup.centralizer_eq_top_iff_subset.mp
  apply top_unique
  rw [← hgen]
  refine sup_le hEY ?_
  rintro _ ⟨a, ha, rfl⟩
  exact (inferInstance : (Subgroup.centralizer (Y : Set G)).Normal).conj_mem
    a (hEY (hAE ha)) t

private theorem bound_commutator_central_of_normal_conjugate_generation
    {H : Type*} [Group H] (A B E Z V K : Subgroup H)
    (hEA : E ≤ A) (hEB : E ≤ B) (hZE : Z ≤ E)
    (hVB : V ≤ B) (hKB : K ≤ B)
    (hVnormal : (V.subgroupOf B).Normal) (hKnormal : (K.subgroupOf B).Normal)
    (hYA : ⁅V, K⁆ ≤ (Subgroup.center A).map A.subtype)
    (t : H) (ht : t ∈ B)
    (hgen : E ⊔ Z.map (MulAut.conj t⁻¹).toMonoidHom = B) :
    ⁅V, K⁆ ≤ (Subgroup.center B).map B.subtype := by
  let VI := V.subgroupOf B
  let KI := K.subgroupOf B
  let YI := ⁅VI, KI⁆
  let EI := E.subgroupOf B
  let ZI := Z.subgroupOf B
  let tI : B := ⟨t, ht⟩
  let _ : VI.Normal := hVnormal
  let _ : KI.Normal := hKnormal
  have hYmap : YI.map B.subtype = ⁅V, K⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVB,
      Subgroup.map_subgroupOf_eq_of_le hKB]
  have hgenI : EI ⊔ ZI.map (MulAut.conj tI⁻¹).toMonoidHom = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEB, Subgroup.map_map]
    have hcomp : B.subtype.comp (MulAut.conj tI⁻¹).toMonoidHom =
        (MulAut.conj t⁻¹).toMonoidHom.comp B.subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (hZE.trans hEB)]
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using hgen
  have hEY : EI ≤ Subgroup.centralizer (YI : Set B) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyAmbient : (y : H) ∈ ⁅V, K⁆ := by
      rw [← hYmap]
      exact Subgroup.mem_map_of_mem B.subtype hy
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp
      (assembly_mapped_center_le_centralizer A (hYA hyAmbient)) e (hEA he)).symm
  have hYcent : YI ≤ Subgroup.center B :=
    central_of_normal_of_conjugate_generation YI EI ZI tI⁻¹
      (fun _ hz => hZE hz) hgenI hEY
  rw [← hYmap]
  exact Subgroup.map_mono hYcent

private theorem bound_finish [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 6 ≤ criticalDistance S) (hf : DistanceTwoShift.Frame S a a' c)
    (hs : DistanceTwoShift.Conclusion S a a' c u) : False := by
  obtain ⟨t, ht, hgen⟩ := criticalPair_exists_generating_conjugator S T hTS hP hSne hA
    u c hs.shifted_critical (by omega)
  have hVct := criticalClosure_le_translated_stabilizer S T hTS hP hSne hA a a' c u hcrit hb hf hs t ht hgen
  let V := criticalClosure S a u
  have hVQa : V ≤ vertexTwoCore S a :=
    criticalClosure_le_core S T hTS hP hSne a u hcrit.1 hs.shifted_critical.1 hs.distance_two (by omega)
  have hVGa : V ≤ stabilizer S a := hVQa.trans (Subgroup.map_subtype_le _)
  have hZuGa : vertexZ S u ≤ stabilizer S a :=
    (vertexZ_le_neighborhoodKernel_of_dist_lt S hs.shifted_critical.1 (by
      rw [SimpleGraph.dist_comm]
      have hdist := hs.distance_two
      omega)).trans (fun _ hz => hz.1)
  have hVnorm := criticalClosure_normal S a u
  have hZaV := vertexZ_self_le_criticalClosure S a u
  have hZuV := vertexZ_le_criticalClosure S a u hZuGa
  obtain ⟨hVGu, hVnormGu, hWGu, hWnorm⟩ :=
    shift_subgroup_and_centerJoin_normal S T hTS hP hSne hA a a' c u hcrit hb hf hs
      t ht hgen V hVQa hVnorm hZaV hZuV hVct
  let K := vertexTwoCore S a ⊓ vertexTwoCore S u
  have hKGu : K ≤ stabilizer S u := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hKnormGu := shift_coreIntersection_normal_of_centerJoin_normal S T hTS hP hSne hA
    a u hcrit.1 hs.shifted_critical.1 (by omega) hs.distance_two hWGu hWnorm
  have hYA : ⁅V, K⁆ ≤ (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype := by
    have hcore := criticalClosure_core_commutator_central S T hTS hP hSne hA a a' c u
      hcrit hb hf hs
    rw [Subgroup.commutator_comm] at hcore
    exact (Subgroup.commutator_mono le_rfl inf_le_left).trans hcore
  let E := edgeTwoCore S u a
  have hEinf : E ≤ stabilizer S u ⊓ stabilizer S a := Subgroup.map_subtype_le _
  obtain ⟨hQaP, hEP⟩ := distanceTwoShift_sharedSylow S T hTS hP hSne hA
    a a' c u hcrit (by omega) hf hs
  have hZE : vertexZ S c ≤ E := by
    change vertexZ S c ≤ edgeTwoCore S u a
    rw [hEP]
    exact le_sup_left
  have hgenE : E ⊔ (vertexZ S c).map (MulAut.conj t⁻¹).toMonoidHom = stabilizer S u := by
    change edgeTwoCore S u a ⊔ _ = _
    rw [hEP]
    simpa [sup_assoc, sup_comm, sup_left_comm] using hgen
  have hYU := bound_commutator_central_of_normal_conjugate_generation
    (stabilizer S a) (stabilizer S u) E (vertexZ S c) V K
    (hEinf.trans inf_le_right) (hEinf.trans inf_le_left) hZE hVGu hKGu
    hVnormGu hKnormGu hYA t ht hgenE
  have hQaGu : vertexTwoCore S a ≤ stabilizer S u := by
    have hQaE : vertexTwoCore S a ≤ E := by simpa only [E, hEP] using hQaP
    exact hQaE.trans (hEinf.trans inf_le_left)
  have hKnormGa := shift_coreIntersection_normal_left_of_bicentral S T hTS hP hSne hA
    a u c hs.shifted_critical (by omega) hQaGu V hVGa hVnorm hZuV hYA hYU
  exact shift_coreIntersection_not_normal_left S T hTS hP hSne hA
    a a' c u hcrit hb hf hs hKnormGa

public theorem criticalDistance_zero_two_or_four [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M))) :
    criticalDistance S = 0 ∨ criticalDistance S = 2 ∨ criticalDistance S = 4 := by
  by_contra hnot
  obtain ⟨a, a', c, u, hb, hcrit, hf, hs⟩ :=
    criticalDistanceBound_initialData S T hTS hP hSne hA hnot
  exact bound_finish S T hTS hP hSne hA a a' c u hcrit hb hf hs

end Stellmacher.PushingUp

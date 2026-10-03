module

public import Stellmacher.PushingUp.ShiftSharedSylow
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# The critical closure and its central core commutator

For M-orbit vertices `a` and `u` at distance two, the source subgroup `V_a`
is the normal closure of `Z_u` in `G_a`, joined with `Z_a`. This module
provides that literal ambient definition, its generator inclusions and
normality, and its containment in `Q_a` when the critical distance exceeds
two. It also shows that `V_a` fixes any vertex `v` with `d(a,v)+2 ≤ b`.

The principal theorem is step (1) of Stellmacher, *Pushing up*, Arch. Math.
46 (1986), proof of (2.4), pp. 12–13: under the chosen critical pair and
distance-two shift with `b ≥ 6`, the commutator `[Q_a,V_a]` is central in
`G_a`. The shared-Sylow theorem puts `Q_a` in `Z_c Q_u`. The shift theorem
makes `[Z_u,Z_c]` central in `G_a`, while the core-center conclusion of (1.3)
makes `[Z_u,Q_u]` trivial. Passing to the quotient by the center extends
the bound to the join, and normal-closure commutator transfer extends it
to all of `V_a`.

The stabilizer containment follows by applying the triangle inequality to
each conjugate of `Z_u`, using that elements of `G_a` fix `a`. The definition
is intentionally exposed so the subsequent containment and bicentral
commutator arguments use exactly the source normal-closure expression.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
open scoped commutatorElement
universe u
variable {M : Type u} [Group M]

private theorem adjacent_of_mOrbit (S : Subgroup M) (a : Vertex S)
    (ha : InMVertexOrbit S a) :
    ∃ b : Vertex S, Adjacent S a b := by
  obtain ⟨g, rfl⟩ := ha
  refine ⟨act S g (hVertex S 1), ?_⟩
  exact (adjacent_act_iff S g (mVertex S 1) (hVertex S 1)).2
    (base_adjacent S)

private theorem vertexZ_le_coreOmega_of_pos [Finite M]
    (S : Subgroup M)
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) :
    vertexZ S a ≤ omegaOneCenterAmbient (vertexTwoCore S a) := by
  obtain ⟨b, hab⟩ := adjacent_of_mOrbit S a ha
  exact
    (criticalDistance_basic S T hTS hP hSne a b ha hab).vertexZ_le_coreOmega_or_distance_zero
      |>.resolve_right (Nat.ne_of_gt hb)

private theorem vertexZ_le_core_of_dist_lt [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    {x y : Vertex S} (hx : InMVertexOrbit S x) (hy : InMVertexOrbit S y)
    (hxy : (cosetGraph S).dist x y < criticalDistance S) :
    vertexZ S x ≤ vertexTwoCore S y := by
  obtain ⟨d, hyd⟩ := adjacent_of_mOrbit S y hy
  rw [← mVertex_neighborhoodKernel_eq_twoCore S T hTS y d hy hyd]
  exact vertexZ_le_neighborhoodKernel_of_dist_lt S hx hxy

private noncomputable def closureLocal
    (S : Subgroup M) (a u : Vertex S) :
    Subgroup (stabilizer S a) :=
  Subgroup.normalClosure
      ((vertexZ S u).subgroupOf (stabilizer S a) :
        Set (stabilizer S a)) ⊔
    (vertexZ S a).subgroupOf (stabilizer S a)

/-- The normal closure of `Z_u` in `G_a`, joined with `Z_a`, in the ambient amalgam. -/
@[expose] public noncomputable def criticalClosure (S : Subgroup M) (a u : Vertex S) :
    Subgroup (FreeAmalgam S) :=
  (Subgroup.normalClosure ((vertexZ S u).subgroupOf (stabilizer S a) :
    Set (stabilizer S a))).map (stabilizer S a).subtype ⊔ vertexZ S a

private theorem criticalClosure_eq_map (S : Subgroup M) (a u : Vertex S) :
    criticalClosure S a u = (closureLocal S a u).map (stabilizer S a).subtype := by
  rw [closureLocal, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le (vertexZ_le_stabilizer S a)]
  rfl

/-- The critical closure lies in the left two-core when the distance exceeds two. -/
public theorem criticalClosure_le_core [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a u : Vertex S)
    (ha : InMVertexOrbit S a) (hu : InMVertexOrbit S u)
    (hau : (cosetGraph S).dist a u = 2)
    (hb : 2 < criticalDistance S) : criticalClosure S a u ≤ vertexTwoCore S a := by
  rw [criticalClosure_eq_map]
  have hZuQa : vertexZ S u ≤ vertexTwoCore S a :=
    vertexZ_le_core_of_dist_lt S T hTS hu ha (by
      simpa [SimpleGraph.dist_comm] using hau ▸ hb)
  have hZaQa : vertexZ S a ≤ vertexTwoCore S a :=
    (vertexZ_le_coreOmega_of_pos S T hTS hP hSne a ha (by omega)).trans
      (fun x hx => (mem_omegaOneCenterAmbient_iff _ x).mp hx |>.1)
  have hZuQ : (vertexZ S u).subgroupOf (stabilizer S a) ≤
      pCore 2 (stabilizer S a) := by
    intro z hz
    obtain ⟨q, hq, heq⟩ := hZuQa hz
    have : q = z := Subtype.ext heq
    rwa [this] at hq
  have hZaQ : (vertexZ S a).subgroupOf (stabilizer S a) ≤
      pCore 2 (stabilizer S a) := by
    intro z hz
    obtain ⟨q, hq, heq⟩ := hZaQa hz
    have : q = z := Subtype.ext heq
    rwa [this] at hq
  exact Subgroup.map_mono (sup_le (Subgroup.normalClosure_le_normal hZuQ) hZaQ)

/-- The shifted vertex center is a generator of the critical closure. -/
public theorem vertexZ_le_criticalClosure (S : Subgroup M) (a u : Vertex S)
    (hZuGa : vertexZ S u ≤ stabilizer S a) : vertexZ S u ≤ criticalClosure S a u := by
  intro z hz
  apply (le_sup_left : _ ≤ criticalClosure S a u)
  exact ⟨⟨z, hZuGa hz⟩, Subgroup.subset_normalClosure hz, rfl⟩

/-- The left vertex center is contained in the critical closure. -/
public theorem vertexZ_self_le_criticalClosure (S : Subgroup M) (a u : Vertex S) :
    vertexZ S a ≤ criticalClosure S a u := le_sup_right

/-- The critical closure is normal in the left vertex stabilizer. -/
public theorem criticalClosure_normal [Finite M] (S : Subgroup M) (a u : Vertex S) :
    ((criticalClosure S a u).subgroupOf (stabilizer S a)).Normal := by
  rw [criticalClosure_eq_map]
  have hnormal : (closureLocal S a u).Normal := by
    let _ := vertexZ_normal_stabilizer S a
    unfold closureLocal
    infer_instance
  convert hnormal using 1
  change Subgroup.comap (stabilizer S a).subtype
    ((closureLocal S a u).map (stabilizer S a).subtype) = _
  exact Subgroup.comap_map_eq_self_of_injective (stabilizer S a).subtype_injective _

private theorem vertexZ_le_stabilizer_of_dist_le [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) {x y : Vertex S}
    (hx : InMVertexOrbit S x)
    (hb : 0 < criticalDistance S)
    (hxy : (cosetGraph S).dist x y ≤ criticalDistance S) :
    vertexZ S x ≤ stabilizer S y := by
  by_cases hlt : (cosetGraph S).dist x y < criticalDistance S
  · intro z hz
    exact (vertexZ_le_neighborhoodKernel_of_dist_lt S hx hlt hz).1
  · have heq : (cosetGraph S).dist x y = criticalDistance S := by omega
    by_cases hker : vertexZ S x ≤ neighborhoodKernel S y
    · intro z hz
      exact (hker hz).1
    · exact (criticalPair_path T hTS hP hSne x y ⟨hx, heq, hker⟩ hb)
        |>.left_Z_le_right_stabilizer

/-- Every vertex within the stated distance bound is fixed by the critical closure. -/
public theorem criticalClosure_le_stabilizer [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥) (a u v : Vertex S)
    (ha : InMVertexOrbit S a) (hu : InMVertexOrbit S u)
    (hb : 0 < criticalDistance S)
    (hau : (cosetGraph S).dist a u = 2)
    (hv : (cosetGraph S).dist a v + 2 ≤ criticalDistance S) :
    criticalClosure S a u ≤ stabilizer S v := by
  let G := stabilizer S a
  rw [criticalClosure_eq_map, closureLocal, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.normalClosure,
      Subgroup.closure_le]
    intro x hx
    obtain ⟨z, hz, hzx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hzx
    have hga : act S (g : FreeAmalgam S) a = a := g.property
    have hd : (cosetGraph S).dist a (act S (g : FreeAmalgam S) v) =
        (cosetGraph S).dist a v := by
      simpa only [hga] using cosetGraph_dist_act S (g : FreeAmalgam S) a v
    have huDist : (cosetGraph S).dist u a = 2 := by
      rwa [SimpleGraph.dist_comm]
    have hdist : (cosetGraph S).dist u (act S (g : FreeAmalgam S) v) ≤
        criticalDistance S := by
      have htri := (cosetGraph_connected S).dist_triangle
        (u := u) (v := a) (w := act S (g : FreeAmalgam S) v)
      omega
    have hzStab : (z : FreeAmalgam S) ∈
        stabilizer S (act S (g : FreeAmalgam S) v) :=
      vertexZ_le_stabilizer_of_dist_le S T hTS hP hSne hu hb hdist hz
    change act S ((g : FreeAmalgam S) * z * (g : FreeAmalgam S)⁻¹) v = v
    change act S (z : FreeAmalgam S) (act S (g : FreeAmalgam S) v) =
      act S (g : FreeAmalgam S) v at hzStab
    rw [act_mul, act_mul, hzStab, ← act_mul]
    simp
  · rw [Subgroup.map_subgroupOf_eq_of_le (vertexZ_le_stabilizer S a)]
    exact vertexZ_le_stabilizer_of_dist_le S T hTS hP hSne ha hb (by omega)


private theorem commutator_sup_le_of_each
    {G : Type u} [Group G] (Q A B Z : Subgroup G) [Z.Normal]
    (hQA : ⁅Q, A⁆ ≤ Z) (hQB : ⁅Q, B⁆ ≤ Z) : ⁅Q, A ⊔ B⁆ ≤ Z := by
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  have hmap (R : Subgroup G) (hR : ⁅Q, R⁆ ≤ Z) :
      R.map q ≤ Subgroup.centralizer (Q.map q : Set (G ⧸ Z)) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm, ← Subgroup.map_commutator,
      Subgroup.map_eq_bot_iff]
    simpa [q, QuotientGroup.ker_mk'] using hR
  have hsup : (A ⊔ B).map q ≤ Subgroup.centralizer (Q.map q : Set (G ⧸ Z)) := by
    rw [Subgroup.map_sup]
    exact sup_le (hmap A hQA) (hmap B hQB)
  have hbot : (⁅Q, A ⊔ B⁆).map q = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hsup
  have hker := (Subgroup.map_eq_bot_iff (f := q) (H := ⁅Q, A ⊔ B⁆)).mp hbot
  simpa [q, QuotientGroup.ker_mk'] using hker

private theorem criticalClosure_stepOne [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u : Vertex S)
    (hcrit : IsCriticalPair S a a')
    (hge : 6 ≤ criticalDistance S)
    (hframe : DistanceTwoShift.Frame S a a' c)
    (hshift : DistanceTwoShift.Conclusion S a a' c u) :
    ⁅pCore 2 (stabilizer S a),
        closureLocal S a u⁆ ≤
      Subgroup.center (stabilizer S a) := by
  let G := stabilizer S a
  let Q : Subgroup G := pCore 2 G
  let A : Subgroup G := (vertexZ S c).subgroupOf G
  let R : Subgroup G := (vertexTwoCore S u).subgroupOf G
  let B : Subgroup G := (vertexZ S u).subgroupOf G
  let Z : Subgroup G := (vertexZ S a).subgroupOf G
  let C : Subgroup G := Subgroup.center G
  have hb : 0 < criticalDistance S := by omega
  have hu : InMVertexOrbit S u := hshift.shifted_critical.1
  have hc : InMVertexOrbit S c :=
    (criticalPair_path T hTS hP hSne u c hshift.shifted_critical hb)
      |>.opposite_inMVertexOrbit
  obtain ⟨d, had⟩ := adjacent_of_mOrbit S a hcrit.1
  obtain ⟨e, hue⟩ := adjacent_of_mOrbit S u hu
  have hlocalA := criticalDistance_basic S T hTS hP hSne a d hcrit.1 had
  have hlocalU := criticalDistance_basic S T hTS hP hSne u e hu hue
  have hshared := distanceTwoShift_sharedSylow S T hTS hP hSne hA
    a a' c u hcrit (by omega) hframe hshift
  have hQaP : vertexTwoCore S a ≤ vertexZ S c ⊔ vertexTwoCore S u := hshared.1
  have hPga : vertexZ S c ⊔ vertexTwoCore S u ≤ stabilizer S a := by
    rw [← hshared.2]
    exact (Subgroup.map_subtype_le _).trans inf_le_right
  have hZcGa : vertexZ S c ≤ stabilizer S a := le_sup_left.trans hPga
  have hQuGa : vertexTwoCore S u ≤ stabilizer S a := le_sup_right.trans hPga
  have hZuGa : vertexZ S u ≤ stabilizer S a := by
    exact (vertexZ_le_neighborhoodKernel_of_dist_lt S hu (by
      rw [SimpleGraph.dist_comm]
      have hdist := hshift.distance_two
      omega)).trans fun _ hx => hx.1
  have hQmap : Q.map G.subtype = vertexTwoCore S a := rfl
  have hAmap : A.map G.subtype = vertexZ S c :=
    Subgroup.map_subgroupOf_eq_of_le hZcGa
  have hRmap : R.map G.subtype = vertexTwoCore S u :=
    Subgroup.map_subgroupOf_eq_of_le hQuGa
  have hBmap : B.map G.subtype = vertexZ S u :=
    Subgroup.map_subgroupOf_eq_of_le hZuGa
  have hQle : Q ≤ A ⊔ R := by
    apply (Subgroup.map_le_map_iff_of_injective G.subtype_injective).mp
    rw [Subgroup.map_sup, hQmap, hAmap, hRmap]
    exact hQaP
  have hBA : ⁅B, A⁆ ≤ C := by
    apply (Subgroup.map_le_map_iff_of_injective G.subtype_injective).mp
    rw [Subgroup.map_commutator, hBmap, hAmap]
    exact hshift.commutator_central_of_two_lt (by omega)
  have hZuQu : vertexZ S u ≤ omegaOneCenterAmbient (vertexTwoCore S u) :=
    hlocalU.vertexZ_le_coreOmega_or_distance_zero.resolve_right
      (Nat.ne_of_gt hb)
  have hBR : ⁅B, R⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro b hbB r hrR
    have hbOmega : (b : FreeAmalgam S) ∈
        omegaOneCenterAmbient (vertexTwoCore S u) := hZuQu hbB
    have hrCore : (r : FreeAmalgam S) ∈ vertexTwoCore S u := hrR
    have hcommAmbient :=
      (mem_omegaOneCenterAmbient_iff (vertexTwoCore S u)
        (b : FreeAmalgam S)).mp hbOmega |>.2.2 (r : FreeAmalgam S) hrCore
    have hcomm : b * r = r * b := by
      apply G.subtype_injective
      simpa using hcommAmbient.symm
    simp [C, commutatorElement_def, hcomm, mul_assoc]
  have hBsup : ⁅B, A ⊔ R⁆ ≤ C :=
    commutator_sup_le_of_each B A R C hBA hBR
  have hBQ : ⁅B, Q⁆ ≤ C :=
    (Subgroup.commutator_mono le_rfl hQle).trans hBsup
  have hQB : ⁅Q, B⁆ ≤ C := by
    rw [Subgroup.commutator_comm]
    exact hBQ
  have hQN : ⁅Q, Subgroup.normalClosure (B : Set G)⁆ ≤ C :=
    Subgroup.commutator_normalClosure_le_of_normal Q B C hQB
  have hZaGa : vertexZ S a ≤ stabilizer S a := vertexZ_le_stabilizer S a
  have hZmap : Z.map G.subtype = vertexZ S a :=
    Subgroup.map_subgroupOf_eq_of_le hZaGa
  have hZaOmega : vertexZ S a ≤
      omegaOneCenterAmbient (vertexTwoCore S a) :=
    hlocalA.vertexZ_le_coreOmega_or_distance_zero.resolve_right
      (Nat.ne_of_gt hb)
  have hQZ : ⁅Q, Z⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro q hq z hz
    have hzOmega : (z : FreeAmalgam S) ∈
        omegaOneCenterAmbient (vertexTwoCore S a) := hZaOmega hz
    have hqCore : (q : FreeAmalgam S) ∈ vertexTwoCore S a := by
      rw [← hQmap]
      exact Subgroup.mem_map_of_mem G.subtype hq
    have hcommAmbient := (mem_omegaOneCenterAmbient_iff (vertexTwoCore S a)
      (z : FreeAmalgam S)).mp hzOmega |>.2.2 (q : FreeAmalgam S) hqCore
    have hcomm : q * z = z * q := by
      apply G.subtype_injective
      simpa using hcommAmbient
    simp [C, commutatorElement_def, hcomm, mul_assoc]
  exact commutator_sup_le_of_each Q
    (Subgroup.normalClosure (B : Set G)) Z C hQN hQZ


/-- The commutator of the left two-core with the critical closure is central. -/
public theorem criticalClosure_core_commutator_central [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 6 ≤ criticalDistance S) (hf : DistanceTwoShift.Frame S a a' c)
    (hs : DistanceTwoShift.Conclusion S a a' c u) :
    ⁅vertexTwoCore S a, criticalClosure S a u⁆ ≤
      (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype := by
  rw [criticalClosure_eq_map]
  have hm := Subgroup.map_mono
    (criticalClosure_stepOne S T hTS hP hSne hA a a' c u hcrit hb hf hs)
    (f := (stabilizer S a).subtype)
  rwa [Subgroup.map_commutator] at hm

end Stellmacher.PushingUp

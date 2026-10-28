module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.TorusKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCoreFixed
public import Theory.GroupAction.PerfectFixedCover

/-!
# Neighboring kernels and odd local actors at distance three

In a nonbinary linear local quotient, the intrinsic actor commutes with
its full permutation kernel modulo the two-core. Coprime lifting through
that two-core makes the centralizer of any odd kernel subgroup transitive
on the neighbors. Source 3.2(c) then kills a common odd subgroup of two
adjacent kernels; their intersection is exactly the core intersection.

For a vertex in the beta orbit, the proved natural core quotient places
every nontrivial odd local actor's core centralizer in the second kernel.
If such an actor lay in a neighboring first kernel, coprime decomposition
would put the entire vertex core in the neighboring core, contradicting
source 6.5. Both assertions transport using the original local markings.
The literal application, with both natural sections and one full path
Cartan retained, is `DistanceThreeNeighborKernels`.

Source: DGS, *Groups and Graphs* (1985), 3.2(c), printed p.72;
9.10(1b)--(3), pp.147--148. These are the kernel arguments used in (3);
the nonadjacent containment of the alpha-minus-one torus is a separate
subsequent step.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem finite_coprime_decomposition (N T : Subgroup G) [Finite N] [Finite T]
    (hn : T ≤ normalizer (N : Set G)) (hs : Group.IsSolvable N)
    (hc : Nat.Coprime (Nat.card T) (Nat.card N)) :
    N = ⁅N,T⁆ ⊔ (N ⊓ centralizer (T : Set G)) := by
  let : Normalizes T N := ⟨hn⟩
  have he := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := N) (A := T) hs hc
  have hm := congrArg (fun U : Subgroup N => U.map N.subtype) he
  rw [Subgroup.map_sup,commutatorAction_subgroup_conj_map_eq_commutator N T hn,
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn N T hn,
    map_subgroupOf_eq_of_le (show subgroupCentralizerIn N T ≤ N from inf_le_left),
    ←MonoidHom.range_eq_map,range_subtype,sup_comm] at hm
  exact hm.symm

/-- The intrinsic actor's commutator with its full permutation kernel lies
in its two-core. The full permutation kernel itself need not be a two-group. -/
theorem nonbinary_actor_kernel_commutator
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (hF : 4 ≤ Nat.card F) :
    ⁅graphLocalGroup (family P) v,ballKernel (family P) v 1⁆ ≤ Q (family P) v := by
  let := finite_endpoints h
  rw [←nonbinary_local_kernel_intersection h hB hS hvw e hF]
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp
      ((ballKernel_le_stabilizer (family P) v 1).trans (sylowGenerated_normalized _)))
    (le_normalizer_iff_commutator_le_right.mp
      ((sylowGenerated_le _).trans (stabilizer_le_normalizer_ballKernel (family P) v 1)))

/-- The natural core quotient's odd-centralizer bound excludes every odd
local actor from a neighboring permutation kernel. Coprime decomposition
would otherwise put the entire vertex core in its neighbor's core. -/
theorem odd_local_actor_disjoint_neighbor_kernel
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    (hfixed : ∀ D : Subgroup G, D ≤ graphLocalGroup (family P) w →
      Odd (Nat.card D) → D ≠ ⊥ →
      Q (family P) w ⊓ centralizer (D : Set G) ≤ ballKernel (family P) w 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (hF : 4 ≤ Nat.card F) (T : Subgroup G)
    (hT : T ≤ graphLocalGroup (family P) w) (ho : Odd (Nat.card T)) :
    Disjoint T (ballKernel (family P) v 1) := by
  let := finite_endpoints h
  let Γ := family P
  let D := T ⊓ ballKernel Γ v 1
  have hDH : D ≤ graphLocalGroup Γ w := inf_le_left.trans hT
  let : Finite T := Finite.of_injective (inclusion (hT.trans (sylowGenerated_le _))) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion (show D ≤ T from inf_le_left)) (inclusion_injective _)
  let : Finite (Q Γ w) := Finite.of_injective (inclusion (Q_le_stabilizer Γ w)) (inclusion_injective _)
  have hDo : Odd (Nat.card D) := ho.of_dvd_nat (card_dvd_of_le (show D ≤ T from inf_le_left))
  apply disjoint_iff.mpr
  change D = ⊥
  by_contra hDn
  have hcentral : Q Γ w ⊓ centralizer (D : Set G) ≤ Q Γ v :=
    two_subgroup_le_Q Γ v (source_kernel_sylow h hB hS v)
      ((isPGroup_pCoreIn 2 _).to_le inf_le_left)
      ((hfixed D hDH hDo hDn).trans (ballKernel_succ_le Γ hvw.symm 1))
  have hcomm : ⁅Q Γ w,D⁆ ≤ Q Γ v :=
    (commutator_mono (neighbor_core_le_localGroup h hB hS hvw)
      (show D ≤ ballKernel Γ v 1 from inf_le_right)).trans
        (nonbinary_actor_kernel_commutator h hB hS hvw e hF)
  have hp : IsPGroup 2 (Q Γ w) := isPGroup_pCoreIn 2 _
  have hcop : Nat.Coprime (Nat.card D) (Nat.card (Q Γ w)) := by
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    rw [hk]
    exact hDo.coprime_two_right.pow_right k
  have hdec := finite_coprime_decomposition (Q Γ w) D
    ((hDH.trans (sylowGenerated_le _)).trans (stabilizer_normalizes_Q Γ w))
    (@IsNilpotent.to_isSolvable _ _ hp.isNilpotent) hcop
  exact hne (hdec.le.trans (sup_le hcomm hcentral))

/-- An odd subgroup of the full permutation kernel has a centralizer
transitive on the actual neighbors. Only its action on the two-core must
be coprime; the intrinsic local actor need not be solvable. -/
theorem nonbinary_kernel_odd_centralizer_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (hF : 4 ≤ Nat.card F) (D : Subgroup G)
    (hD : D ≤ ballKernel (family P) v 1) (ho : Odd (Nat.card D))
    (x y : (graph (family P)).neighborSet v) :
    ∃ g ∈ graphLocalGroup (family P) v ⊓ centralizer (D : Set G),
      g • x.val = y.val := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let N := pCore 2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite D := Finite.of_injective
    (inclusion (hD.trans (ballKernel_le_stabilizer Γ v 1))) (inclusion_injective _)
  have hn : D ≤ normalizer (H : Set G) :=
    (hD.trans (ballKernel_le_stabilizer Γ v 1)).trans (sylowGenerated_normalized _)
  let : MulDistribMulAction D H := conjMulDistribMulActionOfLeNormalizer D H hn
  let : IsInvariant D H N := isInvariant_of_characteristic N
  have hp : IsPGroup 2 N := pCore_isPGroup
  have hcop : Nat.Coprime (Nat.card D) (Nat.card N) := by
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  have hm : ⁅H,D⁆ ≤ N.map H.subtype := by
    have hcore : N.map H.subtype = Q Γ v := graphLocalGroup_core h v
    rw [hcore]
    exact (commutator_mono le_rfl hD).trans
      (nonbinary_actor_kernel_commutator h hB hS hvw e hF)
  have hdis (d : D) (g : H) : g⁻¹ * (d • g) ∈ N := by
    have hh := commutator_le.mp (show ⁅D,H⁆ ≤ N.map H.subtype by
      rw [commutator_comm]; exact hm) d d.property g g.property
    obtain ⟨z,hz,he⟩ := hh
    have hz' : (d • g) * g⁻¹ ∈ N := by
      have he' : z = (d • g) * g⁻¹ := Subtype.ext he
      exact he' ▸ hz
    have heq : QuotientGroup.mk' N (d • g) = QuotientGroup.mk' N g := by
      have he := (QuotientGroup.eq_one_iff (N := N) _).mpr hz'
      change QuotientGroup.mk' N ((d • g) * g⁻¹) = 1 at he
      rw [map_mul,map_inv,mul_inv_eq_one] at he
      exact he
    exact QuotientGroup.eq.mp heq.symm
  obtain ⟨g,hg,hgxy⟩ := graphLocalGroup_transitive h hB hS v x y
  let gH : H := ⟨g,hg⟩
  obtain ⟨n,hnfix⟩ := Theory.GroupAction.exists_fixed_mul_of_solvable_coprime_displacement
    N (@IsNilpotent.to_isSolvable N _ hp.isNilpotent) hcop gH (fun d => hdis d gH)
  have hnQ : ((n : H) : G) ∈ Q Γ v :=
    (graphLocalGroup_core h v).le (mem_map_of_mem H.subtype n.property)
  refine ⟨g * ((n : H) : G),⟨H.mul_mem hg n.val.property,?_⟩,?_⟩
  · intro d hd
    have he := congrArg (fun z : H => (z : G)) (hnfix (⟨d,hd⟩ : D))
    change d * (g * ((n : H) : G)) * d⁻¹ = g * ((n : H) : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · rw [mul_smul]
    have hnK := (source_Z_Q_U h v).2 hnQ
    have hnx : ((n : H) : G) • x.val = x.val :=
      ((ballKernel_one_le_edge Γ x.property) hnK).2
    rw [hnx]
    exact hgxy

/-- The two adjacent full kernels have no nontrivial common odd subgroup.
Their odd centralizer normalizes that subgroup and is locally transitive
at both endpoints, so source 3.2(c) and graph faithfulness apply. -/
theorem odd_adjacent_kernel_intersection_eq_bot
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ev : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,K))
    (hF : 4 ≤ Nat.card F) (hK : 4 ≤ Nat.card K)
    (D : Subgroup G) (hD : D ≤ ballKernel (family P) v 1 ⊓ ballKernel (family P) w 1)
    (ho : Odd (Nat.card D)) : D = ⊥ := by
  apply CommutingNontrivial.source_normalized_edge_eq_bot h hvw D
    (le_inf ((hD.trans inf_le_left).trans (ballKernel_le_stabilizer (family P) v 1))
      ((hD.trans inf_le_right).trans (ballKernel_le_stabilizer (family P) w 1)))
  · intro z hz
    obtain ⟨g,hg,he⟩ := nonbinary_kernel_odd_centralizer_transitive h hB hS hvw ev hF D
      (hD.trans inf_le_left) ho ⟨w,hvw⟩ ⟨z,hz⟩
    exact ⟨g,Subgroup.centralizer_le_normalizer _ hg.2,he⟩
  · intro z hz
    obtain ⟨g,hg,he⟩ := nonbinary_kernel_odd_centralizer_transitive h hB hS hvw.symm ew hK D
      (hD.trans inf_le_right) ho ⟨v,hvw.symm⟩ ⟨z,hz⟩
    exact ⟨g,Subgroup.centralizer_le_normalizer _ hg.2,he⟩

/-- For two adjacent nonbinary linear vertices, the intersection of the
full permutation kernels equals the intersection of their two-cores.
Individual full kernels are not identified with their cores. -/
theorem nonbinary_adjacent_kernel_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ev : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,K))
    (hF : 4 ≤ Nat.card F) (hK : 4 ≤ Nat.card K) :
    ballKernel (family P) v 1 ⊓ ballKernel (family P) w 1 =
      Q (family P) v ⊓ Q (family P) w := by
  let := finite_endpoints h
  let Γ := family P
  let E := stabilizer Γ v ⊓ stabilizer Γ w
  let W := ballKernel Γ v 1 ⊓ ballKernel Γ w 1
  have hWE : W ≤ E := inf_le_left.trans (ballKernel_one_le_edge Γ hvw)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer Γ v from inf_le_left))
    (inclusion_injective _)
  let : Finite W := Finite.of_injective (inclusion hWE) (inclusion_injective _)
  obtain ⟨D,hDW,_,hgen,hcop⟩ := exists_complement_le_of_core_supplement 2 W W le_rfl
    (core_sylow_of_le E W hWE (source_edge_core_sylow h hB hvw))
    (sup_eq_left.mpr (pCoreIn_le 2 W))
  have hDb := odd_adjacent_kernel_intersection_eq_bot h hB hS hvw ev ew hF hK D hDW
    (Nat.coprime_two_left.mp hcop)
  rw [hDb,bot_sup_eq] at hgen
  have hp : IsPGroup 2 W := hgen ▸ isPGroup_pCoreIn 2 W
  exact le_antisymm
    (le_inf (two_subgroup_le_Q Γ v (source_kernel_sylow h hB hS v) hp inf_le_left)
      (two_subgroup_le_Q Γ w (source_kernel_sylow h hB hS w) hp inf_le_right))
    (inf_le_inf (source_Z_Q_U h v).2 (source_Z_Q_U h w).2)

private theorem bool_eq_of_ne {i j k : Bool} (hi : i ≠ k) (hj : j ≠ k) : i = j := by
  cases i <;> cases j <;> cases k <;> simp_all

/-- Both original markings transport to every actual edge. Thus the
adjacent-kernel equality holds throughout the graph, in either orientation. -/
theorem nonbinary_adjacent_kernel_intersection_everywhere
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,K))
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hF : 4 ≤ Nat.card F) (hK : 4 ≤ Nat.card K) :
    ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ballKernel (family P) v 1 ⊓ ballKernel (family P) w 1 =
        Q (family P) v ⊓ Q (family P) w := by
  have oriented (v w : Vertex (family P)) (hvw : (graph (family P)).Adj v w)
      (hv : a.type = v.type) :
      ballKernel (family P) v 1 ⊓ ballKernel (family P) w 1 =
        Q (family P) v ⊓ Q (family P) w := by
    have hw : beta.type = w.type := bool_eq_of_ne
      (hab.1.symm) (hv ▸ hvw.1.symm)
    obtain ⟨g,hg⟩ := (same_orbit_iff (family P) a v).mpr hv
    obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport h g hg
    obtain ⟨k,hk⟩ := (same_orbit_iff (family P) beta w).mpr hw
    obtain ⟨_,f',_,_,_⟩ := local_quotient_parameter_transport h k hk
    exact nonbinary_adjacent_kernel_intersection h hB hS hvw
      (f.symm.trans ea) (f'.symm.trans eb) hK hF
  intro v w hvw
  by_cases hv : a.type = v.type
  · exact oriented v w hvw hv
  · simpa only [inf_comm] using oriented w v hvw.symm (bool_eq_of_ne hv hvw.1.symm)

/-- The entire beta orbit satisfies the neighboring odd-actor exclusion.
The opposite marking is transported from alpha and the noncontainment
is exactly the retained source 6.5 obstruction. -/
theorem odd_local_actor_disjoint_neighbor_kernel_on_orbit
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {a beta : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hfixed : ∀ v : Vertex (family P), beta.type = v.type →
      ∀ D : Subgroup G, D ≤ graphLocalGroup (family P) v →
        Odd (Nat.card D) → D ≠ ⊥ →
          Q (family P) v ⊓ centralizer (D : Set G) ≤ ballKernel (family P) v 2)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,K))
    (hK : 4 ≤ Nat.card K) :
    ∀ v : Vertex (family P), beta.type = v.type →
      ∀ w : Vertex (family P), (graph (family P)).Adj v w →
        ∀ T : Subgroup G, T ≤ graphLocalGroup (family P) v → Odd (Nat.card T) →
          Disjoint T (ballKernel (family P) w 1) := by
  intro v hv w hvw T hT ho
  have hw : a.type = w.type := bool_eq_of_ne hab.1 (hv ▸ hvw.1.symm)
  obtain ⟨g,hg⟩ := (same_orbit_iff (family P) a w).mpr hw
  obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport h g hg
  apply odd_local_actor_disjoint_neighbor_kernel h hB hS hvw.symm ?_ (hfixed v hv)
    (f.symm.trans ea) hK T hT ho
  intro hle
  apply hob v w hvw
  rw [inf_eq_right.mpr hle]
  exact stabilizer_normalizes_Q (family P) v

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

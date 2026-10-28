module

public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.SourceAction
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Parity
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.SymmetricOffender
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport.Foundations

/-!
# Critical-pair completion: parity and elementary conjugate joins

Local Sylow conjugacy proves F.7.9(4) for the actual common Sylow. An injective
ambient map gives the source version when conjugates are taken in a larger
group. Normality of V in G₁ transports the second-base kernel containment to
all first-base neighbors, proving the radius-two step of F.7.11(8).

The geodesic assertion F.7.11(5) needs b ≥ 2. At b = 1 its asserted containment
would make the second module a normal two-subgroup of G₂ and force b > 1;
`not_edge_core_of_track_one` records this incompatibility. These statements do
not assert that a source setup with b = 1 exists. The symmetric offender
theorem applied to the constructed critical witness proves that non-FF forces
odd track. The source core containment then forces b ≥ 3, making the actual
G₂-conjugate join elementary abelian. The trivial seed case is handled directly,
so this last conclusion requires no additional nontriviality hypothesis.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.7.9(4) and
F.7.11(5),(7–8), printed pp.313–314 (PDF pp.324–325).
-/

@[expose] public section

open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base exists_smul_base incident_base)
open CFSG.Quasithin.ChapterF.Section07.Track
open CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- The core of either base stabilizer fixes its first ball. -/
theorem base_core_le_kernel (D : SourceSetup F) (i : Bool) :
    (F i).pCoreIn 2 ≤ ballKernel F (base F i) 1 := by
  have hT : (D.sylow i : Subgroup (F i)).map (F i).subtype ≤ F (!i) := by
    cases i
    · rw [D.same_sylow]
      exact map_subtype_le _
    · rw [← D.same_sylow]
      exact map_subtype_le _
  have hk := CFSG.Quasithin.ChapterF.LocalCores.kernel_core_eq_vertex_core
    (F i) (F (!i)) (D.sylow i) hT
  have hedge : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, incident_base F i (!i)⟩
  have hball := ballKernel_one_eq_map_normalCore F hedge
  rw [show stabilizer F (base F i) = F i from stabilizer_base F i,
    show stabilizer F (base F (!i)) = F (!i) from stabilizer_base F (!i)] at hball
  rw [← hk]
  exact (pCoreIn_le 2 _).trans hball.ge

/-- Transport the second-base kernel bound to all neighbors using normality only in G₁. -/
theorem seed_le_neighbor_kernel (D : SourceSetup F)
    (hcore : D.seed ≤ (F true).pCoreIn 2)
    {u : Vertex F} (hu : (graph F).Adj (base F false) u) :
    D.seed ≤ ballKernel F u 1 := by
  have hedge : (graph F).Adj (base F false) (base F true) :=
    ⟨Bool.false_ne_true, incident_base F false true⟩
  obtain ⟨g, hg, hgu⟩ := locally_transitive F hedge hu
  have hgF : g ∈ F false := by
    simpa only [stabilizer, base, stabilizer_base] using hg
  have hn : D.seed.map (MulAut.conj g).toMonoidHom = D.seed :=
    mem_normalizer_iff_map_conj_eq.mp (D.seed_normalized hgF)
  have h := map_mono (f := (MulAut.conj g).toMonoidHom)
    (hcore.trans (base_core_le_kernel F D true))
  rwa [hn, ← ballKernel_translate, hgu] at h

/-- The actual source core hypothesis implies that the track exceeds one. -/
theorem one_lt_track_of_true_core (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hcore : D.seed ≤ (F true).pCoreIn 2) : 1 < D.track hne := by
  have hfix : D.seed ≤ ballKernel F (base F false) 2 := by
    intro x hx w hw
    rw [mem_ball_iff F D.generates (base F false) w 2] at hw
    by_cases hle : (graph F).dist (base F false) w ≤ 1
    · exact D.seed_le_first_kernel hx w
        ((mem_ball_iff F D.generates (base F false) w 1).mpr hle)
    · have hd : (graph F).dist (base F false) w = 2 := by omega
      have hne' : base F false ≠ w := by
        intro h
        subst w
        simp at hd
      obtain ⟨u, huw, hu⟩ := exists_predecessor F D.generates (base F false) w hne'
      have hu1 : (graph F).dist (base F false) u = 1 := by omega
      exact seed_le_neighbor_kernel F D hcore
        (SimpleGraph.dist_eq_one_iff_adj.mp hu1) hx w
        ((mem_ball_one F u w).mpr (Or.inl huw.symm))
  have := ((D.track_spec hne).2.2.2 2).mp hfix
  omega

/-- Local Sylow conjugacy puts any conjugate of the seed contained in G₂
in its two-core, under the actual zeroth weak-closure hypothesis. -/
theorem conjugate_seed_le_true_core (D : SourceSetup F)
    (hW : indexedWeakClosure D.seed
      ((D.sylow true : Subgroup (F true)).map (F true).subtype) 0 ≤ (F true).pCoreIn 2)
    (g : G) (hg : D.seed.map (MulAut.conj g).toMonoidHom ≤ F true) :
    D.seed.map (MulAut.conj g).toMonoidHom ≤ (F true).pCoreIn 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite (F true) := D.finite true
  let := D.reduced.elementary
  let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
  let W := D.seed.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hWp : IsPGroup 2 (W.subgroupOf (F true)) :=
    (IsElementaryAbelian.isPGroup 2 W).comap_subtype
  obtain ⟨P, hP⟩ := hWp.exists_le_sylow
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq (F true) P (D.sylow true)
  have hlocal : (W.subgroupOf (F true)).map (MulAut.conj t).toMonoidHom ≤
      (D.sylow true : Subgroup (F true)) := by
    rw [← ht]
    exact map_mono hP
  have hcomp : (F true).subtype.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (t : G)).toMonoidHom.comp (F true).subtype := by
    ext x
    rfl
  have hamb := map_mono (f := (F true).subtype) hlocal
  rw [map_map, hcomp, ← map_map, map_subgroupOf_eq_of_le hg] at hamb
  have hgen : W.map (MulAut.conj (t : G)).toMonoidHom ≤
      indexedWeakClosure D.seed
        ((D.sylow true : Subgroup (F true)).map (F true).subtype) 0 := by
    apply gamma_le_weakClosure
    apply (mem_gamma_zero_iff _ _ _).mpr
    exact ⟨(t : G) * g, offender_map_conj_map D.seed g (t : G), hamb⟩
  have h := map_mono (f := (MulAut.conj (t : G)⁻¹).toMonoidHom) (hgen.trans hW)
  rw [offender_map_conj_inverse] at h
  have hn : (F true).map (MulAut.conj (t : G)⁻¹).toMonoidHom = F true :=
    mem_normalizer_iff_map_conj_eq.mp ((F true).le_normalizer ((F true).inv_mem t.property))
  rw [← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
    2 _ (MulAut.conj (t : G)⁻¹).injective, hn] at h
  exact h

/-- F.7.9(4): the source weak-closure condition forces even track.
All Sylow conjugacy occurs in the finite second vertex group. -/
theorem even_track_of_weakClosure_core (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hW : indexedWeakClosure D.seed
      ((D.sylow false : Subgroup (F false)).map (F false).subtype) 0 ≤ (F true).pCoreIn 2) :
    Even (D.track hne) := by
  by_contra heven
  have hodd := (Nat.even_or_odd (D.track hne)).resolve_left heven
  obtain ⟨v, hd, hcrit⟩ := (D.critical_witness hne).1
  have hv := odd_endpoint_type F D hne hd hodd
  obtain ⟨g, hg⟩ := exists_smul_base F v
  rw [hv] at hg
  have hle : D.seed ≤ stabilizer F v := by
    intro x hx
    exact (D.track_spec hne).2.1 hx v ((mem_ball_iff F D.generates _ _ _).mpr hd.le)
  have hbase : D.seed.map (MulAut.conj g⁻¹).toMonoidHom ≤ F true := by
    have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    rw [← stabilizer_translate, ← hg, inv_smul_smul] at h
    simpa only [stabilizer, base, stabilizer_base] using h
  rw [D.same_sylow] at hW
  have hc := (conjugate_seed_le_true_core F D hW g⁻¹ hbase).trans
    (base_core_le_kernel F D true)
  have h := map_mono (f := (MulAut.conj g).toMonoidHom) hc
  have hinv := offender_map_conj_inverse D.seed g⁻¹
  rw [inv_inv] at hinv
  rw [hinv, ← ballKernel_translate, hg] at h
  exact hcrit h

/-- At radius one the unqualified printed edge-core assertion cannot hold.
Its second-type module would be a normal two-subgroup of G₂, forcing radius two. -/
theorem not_edge_core_of_track_one (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hb : D.track hne = 1) :
    ¬ vertexModule F D.seed (base F true) ≤ (F false ⊓ F true).pCoreIn 2 := by
  intro h
  have hp : IsPGroup 2 (vertexModule F D.seed (base F true)) :=
    (isPGroup_pCoreIn 2 (F false ⊓ F true)).of_injective
      (inclusion h) (inclusion_injective h)
  have hn : F true ≤ normalizer (vertexModule F D.seed (base F true) : Set G) := by
    simpa only [stabilizer, base, stabilizer_base] using
      stabilizer_normalizes_vertexModule F D.seed D.seed_normalized (base F true)
  have hc : vertexModule F D.seed (base F true) ≤ (F true).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp (h.trans ((pCoreIn_le 2 _).trans inf_le_right)) hn
  have hseed : D.seed ≤ vertexModule F D.seed (base F true) := by
    have h := firstModule_le_vertexModule_of_adj F D.seed (v := base F true)
      (w := base F false) rfl
      ⟨by change true ≠ false; decide, incident_base F true false⟩
    rwa [firstModule_base F D.seed D.seed_normalized] at h
  have := one_lt_track_of_true_core F D hne (hseed.trans hc)
  omega

/-- F.7.11(5) for an actual geodesic, with its necessary b ≥ 2 boundary. -/
theorem geodesic_edge_core_of_walk (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {v : Vertex F} (hd : (graph F).dist (base F false) v = D.track hne)
    (hb : 2 ≤ D.track hne) (p : (graph F).Walk (base F false) v)
    (hp : p.length = (graph F).dist (base F false) v)
    (hs : p.getVert 1 = base F true) :
    vertexModule F D.seed (base F true) ≤
      (stabilizer F (p.getVert (p.length - 1)) ⊓ stabilizer F v).pCoreIn 2 := by
  have hlen : p.length = D.track hne := hp.trans hd
  have hpen := p.adj_getVert_succ (i := p.length - 1) (by omega)
  have hlast : p.length - 1 + 1 = p.length := by omega
  rw [hlast, p.getVert_length] at hpen
  have hseg := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take (p.length - 1)))
    ((p.take (p.length - 1)).isSubwalk_drop 1)
  have hstart : (p.take (p.length - 1)).getVert 1 = base F true := by
    rw [SimpleGraph.Walk.take_getVert, min_eq_right (by omega), hs]
  rw [SimpleGraph.Walk.drop_length, SimpleGraph.Walk.take_length,
    min_eq_left (Nat.sub_le _ _), hstart] at hseg
  exact geodesic_edge_core F D hne rfl (by omega) hpen

/-- An inclusion of ambient groups preserves all zero-corank generators.
The larger ambient group may supply additional conjugates. -/
theorem weakClosure_zero_map_le {K : Type*} [Group K]
    (f : G →* K) (V T : Subgroup G) :
    (indexedWeakClosure V T 0).map f ≤ indexedWeakClosure (V.map f) (T.map f) 0 := by
  rw [map_le_iff_le_comap, weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g, rfl, hT⟩ := (mem_gamma_zero_iff V T A).mp hA
  apply map_le_iff_le_comap.mp
  apply gamma_le_weakClosure
  apply (mem_gamma_zero_iff _ _ _).mpr
  refine ⟨f g, ?_, map_mono hT⟩
  rw [map_map, map_map]
  congr 1
  ext x
  simp

/-- F.7.9(4) when weak closure is taken in a larger ambient group, as in
F.7.1. The inclusion is literal, and the smaller closure is only contained in it. -/
theorem even_track_of_ambient_weakClosure_core (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {K : Type*} [Group K] (f : G →* K) (hf : Function.Injective f)
    (hW : indexedWeakClosure (D.seed.map f)
      (((D.sylow false : Subgroup (F false)).map (F false).subtype).map f) 0 ≤
        ((F true).map f).pCoreIn 2) :
    Even (D.track hne) := by
  apply even_track_of_weakClosure_core F D hne
  apply (map_le_map_iff_of_injective hf).mp
  rw [← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 f hf]
  exact (weakClosure_zero_map_le f D.seed _).trans hW

/-- The elementary conclusion of F.7.11(8) once odd parity is known.
The core premise supplies radius two; oddness then forces b ≥ 3. -/
theorem conjugate_join_elementary_of_odd (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hcore : D.seed ≤ (F true).pCoreIn 2) (hodd : Odd (D.track hne)) :
    IsElementaryAbelian 2 (↥(⨆ g : F true,
      D.seed.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G)) := by
  have hsmall := one_lt_track_of_true_core F D hne hcore
  have hb : 2 < D.track hne := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rw [← second_base_module_eq_conjugate_join F D.seed D.seed_normalized]
  exact secondModule_elementary F D hne hb rfl

/-- F.7.11(7) for the faithful action of the literal quotient G₁/C_G₁(V).
The critical witness and the symmetric offender theorem discharge every
extra premise of the conditional parity argument. Nontriviality is needed
only to define the track. -/
theorem odd_track_of_not_ff (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hnot : ¬ SourceAction.IsFF D) : Odd (D.track hne) := by
  apply (Nat.even_or_odd (D.track hne)).resolve_left
  intro heven
  obtain ⟨v, hd, hcritical⟩ := (D.critical_witness hne).1
  exact hnot (SymmetricOffender.even_critical_pair_isFF D hne hd heven hcritical)

/-- F.7.11(8): the actual G₂-conjugate join is elementary abelian under the
source core and non-FF hypotheses. The trivial V case is included without
attempting to define a greatest fixed radius for it. -/
theorem conjugate_join_elementary_of_not_ff (D : SourceSetup F)
    (hcore : D.seed ≤ (F true).pCoreIn 2) (hnot : ¬ SourceAction.IsFF D) :
    IsElementaryAbelian 2 (↥(⨆ g : F true,
      D.seed.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G)) := by
  by_cases hzero : D.V = ⊥
  · have hseed : D.seed = ⊥ := by simp [SourceSetup.seed, hzero]
    have hjoin : (⨆ g : F true,
        D.seed.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) = D.seed := by
      simp [hseed]
    rw [hjoin]
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let := D.reduced.elementary
    exact IsElementaryAbelian.map (F false).subtype
  · exact conjugate_join_elementary_of_odd F D hzero hcore
      (odd_track_of_not_ff F D hzero hnot)

end CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion

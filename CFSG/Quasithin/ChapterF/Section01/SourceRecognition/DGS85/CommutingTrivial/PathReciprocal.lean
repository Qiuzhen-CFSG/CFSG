module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.RankOnePaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalPaths

/-!
# The path-orbit argument and unrestricted reciprocal escape

The first nonregular path exists across both vertex orbits. A suffix with
an escaping two-subgroup is regular at a linear endpoint: the full edge
has normal Sylow two-subgroup, and source 6.8 controls the path-fixer core.
Apply this to the path from beta to alpha-prime. A nonregular endpoint
must have the opposite type. If the reverse span lay in Q_beta, its action
would fix the extended reverse path ending at alpha and force regularity
there too. For longer first nonregular length, path reversal directly
exchanges beta and alpha-prime. This proves reverse escape for every b.

The same argument proves 9.5's orbit implication for the actual first
nonregular length and every longer path. The full permutation kernel U
and the vertex two-core Q remain distinct. No tree hypothesis is used.
Source: DGS, Groups and Graphs (1985), 9.5--9.7, printed pp.143--145.
-/

@[expose] public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem bool_eq_of_ne {i j k : Bool} (hi : i ≠ k) (hj : j ≠ k) : i = j := by
  cases i <;> cases j <;> cases k <;> simp_all

/-- A two-subgroup fixing a path and escaping its linear terminal core
forces regularity of every first-length path of the same endpoint type. -/
theorem linear_terminal_regular_of_escape
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {s n : ℕ} (hsn : s + 1 ≤ n + 1)
    (hshort : ∀ k x (q : BasedWalk (graph (family P)) k x),
      k < s+1 → q.Nonbacktracking → Regular (A := G) q)
    {v x : Vertex (family P)}
    (p : BasedWalk (graph (family P)) (n+1) v)
    (q : BasedWalk (graph (family P)) (s+1) x)
    (hp : p.Nonbacktracking) (hq : q.Nonbacktracking)
    (ht : p.endpoint.type = q.endpoint.type)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (family P) p.endpoint ⧸
      pCore 2 (graphLocalGroup (family P) p.endpoint)) ≃* SL(2,K))
    (A : Subgroup G) (hpA : IsPGroup 2 A)
    (hAp : A ≤ pathStabilizer (family P) p) (hAQ : ¬ A ≤ Q (family P) p.endpoint) :
    RightRegular (A := G) q := by
  let := finite_endpoints h
  by_contra hbad
  obtain ⟨y,r,hr,hbad,he,_,hsub⟩ :=
    Noncommuting.graph_singular_terminal_subpath hsn hshort p q hp hq hbad ht
  have hAr : A ≤ pathStabilizer (family P) r := fun _ ha z hz => hAp ha z (hsub z hz)
  let E := stabilizer (family P) r.endpoint ⊓ stabilizer (family P) r.penultimate
  have hem : r.endpoint ∈ r.vertices := by
    simpa only [BasedWalk.support_toWalk] using r.toWalk.end_mem_support
  have hpm : r.penultimate ∈ r.vertices := by
    have hh := (r.take s (Nat.le_succ s)).toWalk.end_mem_support
    rw [BasedWalk.support_toWalk,BasedWalk.endpoint_take_penultimate,BasedWalk.vertices_take] at hh
    exact List.mem_of_mem_take hh
  have hDE : pathStabilizer (family P) r ≤ E :=
    pathStabilizer_le_edge (family P) r hem hpm
  let : Finite E := Finite.of_injective
    (inclusion (show E ≤ stabilizer (family P) r.endpoint from inf_le_left)) (inclusion_injective _)
  let : Finite (pathStabilizer (family P) r) := Finite.of_injective (inclusion hDE) (inclusion_injective _)
  have hcore := pGroup_le_core_of_core_sylow (pathStabilizer (family P) r) A hAr hpA
    (core_sylow_of_le E _ hDE (source_edge_core_sylow h hB r.adj_penultimate_endpoint.symm))
  let e' : (graphLocalGroup (family P) r.endpoint ⧸
      pCore 2 (graphLocalGroup (family P) r.endpoint)) ≃* SL(2,K) := he.symm ▸ e
  have hact : GraphAction (graph (family P)) G :=
    ⟨fun g _ _ he => (Subgroup.CosetGeometry.translationGraphIso (family P) g).toHom.map_adj he⟩
  have htrans := rootPathTransitive_of_short_rightRegular hact (s+1)
    (fun k x p hk hp => (hshort k x p hk hp).2) y (s+1) le_rfl
  have hnot : ¬ ∀ x z : (graph (family P)).neighborSet r.endpoint,
      x.val ≠ r.penultimate → z.val ≠ r.penultimate →
        ∃ g ∈ pathStabilizer (family P) r, g • x.val = z.val := by
    intro hh
    apply hbad
    intro x z hx hz
    exact hh ⟨x,hx.1⟩ ⟨z,hz.1⟩ hx.2 hz.2
  have hle := source_path_core_le_endpoint_core h hB hS (source_rankOne_branching h)
    htrans r hr e' hnot
  apply hAQ
  rw [←he]
  exact hcore.trans hle

private theorem path_vertex_dist_le {n : ℕ} {v z : Vertex (family P)}
    (p : BasedWalk (graph (family P)) n v) (hz : z ∈ p.vertices) :
    (graph (family P)).dist v z ≤ n := by
  classical
  have hm : z ∈ p.toWalk.support := by rwa [BasedWalk.support_toWalk]
  have hh := (graph (family P)).dist_le (p.toWalk.takeUntil z hm)
  have hl := p.toWalk.length_takeUntil_le_length hm
  rw [BasedWalk.length_toWalk] at hl
  exact hh.trans hl

/-- The distance budget makes the closed-ball span fix the whole path. -/
theorem V_le_pathStabilizer (h : LocallyRankOneTriple P B)
    {n r : ℕ} {v : Vertex (family P)} (p : BasedWalk (graph (family P)) n v)
    (hn : n + r ≤ b (family P)) :
    V (family P) v r ≤ pathStabilizer (family P) p := by
  intro a ha z hz
  exact V_le_stabilizer (family P) h.generate v z
    (by have hh := path_vertex_dist_le p hz; omega) ha

/-- The unrestricted escape assertion of 9.6, using the actual adjacent
linear quotients. In particular, b = 3 is not a hypothesis. -/
theorem linear_critical_reciprocal_escape
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta a' : Vertex (family P)}
    (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 2 < b (family P)) (hodd : Odd (b (family P)))
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (eα : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,F))
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,K)) :
    ¬ V (family P) a' 1 ≤ Q (family P) beta := by
  let Γ := family P
  let := finite_endpoints h
  have hZ := fun v => (source_Z_Q_U h v).1
  let := V_elementary Γ h.generate hZ (source_kernel_sylow h hB hS) beta (r := 1) (by omega)
  let := V_elementary Γ h.generate hZ (source_kernel_sylow h hB hS) a' (r := 1) (by omega)
  have hforward : ¬ V Γ beta 1 ≤ Q Γ a' :=
    V_not_le_Q_of_criticalPair Γ hc hab.symm (source_Z_Q_U h a').2
  have hat : a.type ≠ a'.type := (odd_dist_iff Γ h.generate a a').mp (hc.1.symm ▸ hodd)
  have hbt : beta.type = a'.type := by
    exact bool_eq_of_ne hab.1.symm hat.symm
  obtain ⟨t,ht⟩ := (same_orbit_iff Γ beta a').mpr hbt
  obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport h t ht
  let eβ' := f.symm.trans eβ
  change (graph Γ).dist beta a' + 1 = b Γ at hd
  change 2 < b Γ at hb
  obtain ⟨n,hlen⟩ : ∃ n, (graph Γ).dist beta a' = n+1 :=
    ⟨(graph Γ).dist beta a' - 1, by omega⟩
  obtain ⟨p,hp,hpe⟩ : ∃ p : BasedWalk (graph Γ) (n+1) beta,
      p.Nonbacktracking ∧ p.endpoint = a' := by
    rw [←hlen]
    exact BasedWalk.exists_geodesic ((connected Γ h.generate) beta a')
  have hnb : n+1+1 = b Γ := by omega
  have hfix : V Γ beta 1 ≤ pathStabilizer Γ p := V_le_pathStabilizer h p hnb.le
  let ep : (graphLocalGroup Γ p.endpoint ⧸ pCore 2 (graphLocalGroup Γ p.endpoint)) ≃* SL(2,K) :=
    hpe.symm ▸ eβ'
  obtain ⟨s,hs,_,i,q,hq,hbad,_,_⟩ := source_first_nonregular_path h hS
  have hshort := fun k x q hk hq => hs k hk x q hq
  have hact : GraphAction (graph Γ) G :=
    ⟨fun g _ _ he => (Subgroup.CosetGeometry.translationGraphIso Γ g).toHom.map_adj he⟩
  intro hsmall
  by_cases hlong : n+1 ≤ s+1
  · obtain ⟨g,hg⟩ := arcTransitive_of_short_rightRegular hact (s+1)
      (fun k x q hk hq => (hshort k x q hk hq).2) hlong p (reverse p) hp
      (nonbacktracking_reverse p hp) ((same_orbit_iff Γ _ _).mpr (by rw [hpe]; exact hbt))
    have hg₂ : g • a' = beta := by
      simpa only [hpe,endpoint_reverse] using endpoint_smul_of_vertices hact g p (reverse p) hg
    have hgr : (reverse p).vertices.map (g • ·) = p.vertices := by
      rw [vertices_reverse,List.map_reverse,hg,vertices_reverse,List.reverse_reverse]
    have hg₁ : g • beta = a' := by
      simpa only [hpe,endpoint_reverse] using endpoint_smul_of_vertices hact g (reverse p) p hgr
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hsmall
    rw [←V_translate,←Q_translate,hg₁,hg₂] at hm
    exact hforward hm
  · have hqt : q.endpoint.type ≠ a'.type := by
      intro hh
      exact hbad (linear_terminal_regular_of_escape h hB hS (by omega) hshort p q hp hq
        (by rw [hpe,hh]) ep (V Γ beta 1) (IsElementaryAbelian.isPGroup 2 _) hfix
        (by rw [hpe]; exact hforward))
    have hqa : a.type = q.endpoint.type := by
      exact bool_eq_of_ne hat hqt
    let r := (reverse p).snoc (show (graph Γ).Adj (reverse p).endpoint a from by
      rw [endpoint_reverse]; exact hab.symm)
    have hre : r.endpoint = a := endpoint_snoc _ _
    have hr : r.Nonbacktracking := nonbacktracking_of_geodesic r (by
      rw [hre,hpe,SimpleGraph.dist_comm,hc.1]; exact hnb.symm)
    have hfix' : V Γ a' 1 ≤ pathStabilizer Γ r := by
      have hpre : V Γ a' 1 ≤ pathStabilizer Γ (reverse p) := by
        have hh := V_le_pathStabilizer h (reverse p) (r := 1) hnb.le
        rw [show V Γ a' 1 = V Γ p.endpoint 1 from congrArg (fun v => V Γ v 1) hpe.symm]
        exact hh
      have hlast : V Γ a' 1 ≤ stabilizer Γ a :=
        (hsmall.trans (source_Z_Q_U h beta).2).trans
          ((ballKernel_one_le_edge Γ hab.symm).trans inf_le_right)
      intro g hg z hz
      rw [BasedWalk.vertices_snoc,List.mem_append,List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hpre hg z hz
      · exact hlast hg
    have hescape : ¬ V Γ a' 1 ≤ Q Γ a := by
      intro hh
      apply hc.2
      apply le_trans (le_inf (Z_le_stabilizer_of_dist_le_b Γ h.generate a a' hc.1.le) ?_)
        (neighborhood_centralizer_le_U h a')
      exact hZ a |>.trans (fun x hx => centralizer_le hh ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
    let er : (graphLocalGroup Γ r.endpoint ⧸ pCore 2 (graphLocalGroup Γ r.endpoint)) ≃* SL(2,F) :=
      hre.symm ▸ eα
    exact hbad (linear_terminal_regular_of_escape h hB hS (by omega) hshort r q hr hq
      (by rw [hre]; exact hqa) er (V Γ a' 1) (IsElementaryAbelian.isPGroup 2 _) hfix'
      (by rw [hre]; exact hescape))

/-- Source 9.5: a path core escaping the full terminal kernel can end only
in the alpha-prime orbit. Longer paths satisfy the same implication. -/
theorem critical_path_core_escape_type
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta a' : Vertex (family P)}
    (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 2 < b (family P)) (hodd : Odd (b (family P)))
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (eα : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,F))
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,K))
    {s : ℕ}
    (hshort : ∀ k x (q : BasedWalk (graph (family P)) k x),
      k < s+1 → q.Nonbacktracking → Regular (A := G) q)
    {x : Vertex (family P)} (q : BasedWalk (graph (family P)) (s+1) x)
    (hq : q.Nonbacktracking) (hbad : ¬ RightRegular (A := G) q)
    (hs : s+1 < b (family P))
    {n : ℕ} {v : Vertex (family P)} (r : BasedWalk (graph (family P)) (n+1) v)
    (hr : r.Nonbacktracking) (hsn : s+1 ≤ n+1)
    (hesc : ¬ (pathStabilizer (family P) r).pCoreIn 2 ≤ U (family P) r.endpoint) :
    r.endpoint.type = a'.type := by
  let Γ := family P
  let := finite_endpoints h
  have hZ := fun v => (source_Z_Q_U h v).1
  let := V_elementary Γ h.generate hZ (source_kernel_sylow h hB hS) beta (r := 1) (by omega)
  have hforward : ¬ V Γ beta 1 ≤ Q Γ a' :=
    V_not_le_Q_of_criticalPair Γ hc hab.symm (source_Z_Q_U h a').2
  have hat : a.type ≠ a'.type := (odd_dist_iff Γ h.generate a a').mp (hc.1.symm ▸ hodd)
  have hbt : beta.type = a'.type := by
    exact bool_eq_of_ne hab.1.symm hat.symm
  obtain ⟨t,ht⟩ := (same_orbit_iff Γ beta a').mpr hbt
  obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport h t ht
  let eβ' := f.symm.trans eβ
  change (graph Γ).dist beta a' + 1 = b Γ at hd
  change 2 < b Γ at hb
  change s+1 < b Γ at hs
  obtain ⟨m,hlen⟩ : ∃ m, (graph Γ).dist beta a' = m+1 :=
    ⟨(graph Γ).dist beta a' - 1, by omega⟩
  obtain ⟨p,hp,hpe⟩ : ∃ p : BasedWalk (graph Γ) (m+1) beta,
      p.Nonbacktracking ∧ p.endpoint = a' := by
    rw [←hlen]
    exact BasedWalk.exists_geodesic ((connected Γ h.generate) beta a')
  have hmb : m+1+1 = b Γ := by omega
  have hfix : V Γ beta 1 ≤ pathStabilizer Γ p := V_le_pathStabilizer h p hmb.le
  let ep : (graphLocalGroup Γ p.endpoint ⧸ pCore 2 (graphLocalGroup Γ p.endpoint)) ≃* SL(2,K) :=
    hpe.symm ▸ eβ'
  have hqt : q.endpoint.type ≠ a'.type := by
    intro hh
    exact hbad (linear_terminal_regular_of_escape h hB hS (by omega) hshort p q hp hq
      (by rw [hpe,hh]) ep (V Γ beta 1) (IsElementaryAbelian.isPGroup 2 _) hfix
      (by rw [hpe]; exact hforward))
  by_contra hrt
  have hra : a.type = r.endpoint.type := by
    exact bool_eq_of_ne hat hrt
  have hrq : r.endpoint.type = q.endpoint.type := by
    exact bool_eq_of_ne hrt hqt
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ a r.endpoint).mpr hra
  obtain ⟨_,fα,_,_,_⟩ := local_quotient_parameter_transport h g hg
  exact hbad (linear_terminal_regular_of_escape h hB hS hsn hshort r q hr hq hrq
    (fα.symm.trans eα) ((pathStabilizer Γ r).pCoreIn 2) (isPGroup_pCoreIn 2 _)
    (pCoreIn_le 2 _) (fun hh => hesc (hh.trans (source_Z_Q_U h r.endpoint).2)))

/-- The first nonregular length is taken across both vertex orbits. The
last clause is the source 9.5 implication, also for longer paths. -/
def CriticalPathOrbit (Γ : Bool → Subgroup G) (a' : Vertex Γ) : Prop :=
  ∃ s : ℕ, 0 < s ∧
    (∀ k < s, ∀ v (p : BasedWalk (graph Γ) k v),
      p.Nonbacktracking → Regular (A := G) p) ∧
    (∀ v, ∀ k ≤ s, RootPathTransitive (graph Γ) G v k) ∧
    (∃ v, ∃ p : BasedWalk (graph Γ) s v,
      p.Nonbacktracking ∧ ¬ RightRegular (A := G) p) ∧
    (s < b Γ → ∀ n, s ≤ n → ∀ v (p : BasedWalk (graph Γ) n v),
      p.Nonbacktracking → ¬ (pathStabilizer Γ p).pCoreIn 2 ≤ U Γ p.endpoint →
      ∃ g : G, g • p.endpoint = a')

/-- Construct the first nonregular path and its 9.5 orbit implication from
the actual local groups and the original critical pair. -/
theorem critical_first_path_orbit
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta a' : Vertex (family P)}
    (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 2 < b (family P)) (hodd : Odd (b (family P)))
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (eα : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,F))
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,K)) :
    CriticalPathOrbit (family P) a' := by
  obtain ⟨s,hs,ht,i,q,hq,hbad,_,_⟩ := source_first_nonregular_path h hS
  refine ⟨s+1,by omega,hs,ht,⟨_,q,hq,hbad⟩,?_⟩
  intro hsb n hsn v p hp hesc
  cases n with
  | zero => omega
  | succ n =>
    exact (same_orbit_iff (family P) p.endpoint a').mpr
      (critical_path_core_escape_type h hB hS hc hab hd hb hodd eα eβ
        (fun k x q hk hq => hs k hk x q hq) q hq hbad hsb p hp hsn hesc)

/-- The minimal-distance part of 9.7 lies in the intrinsic local group,
not just the full stabilizer. This works for any closed-ball radius. -/
theorem span_le_localGroup_of_distance (h : LocallyRankOneTriple P B)
    (v w : Vertex (family P)) {r : ℕ}
    (hd : (graph (family P)).dist v w + r ≤ b (family P)) :
    V (family P) v r ≤ graphLocalGroup (family P) w := by
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  apply center_le_localGroup_of_dist_le_b h
  have hz' := (mem_ball_iff (family P) h.generate v z r).mp hz
  have ht := (connected (family P) h.generate).dist_triangle (u := z) (v := v) (w := w)
  rw [SimpleGraph.dist_comm (u := z) (v := v)] at ht
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

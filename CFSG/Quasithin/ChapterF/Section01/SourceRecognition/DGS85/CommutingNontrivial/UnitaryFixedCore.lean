module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryComparison
public import Theory.GroupTheory.CentralizerDisplacementNormalization

/-!
# Trapped fixed subgroups at a large unitary moving center

An elementary subgroup of the beta core acts on every neighboring center.
If it fixes the opposite core intersection, its centralizer index on the
whole beta span is at most that intersection's index. A nontrivial action
on a neighboring center would instead have index at least the square of
the moving unitary field order, by the actual same-orbit center estimate.
Below that square bound it therefore fixes the whole span.

The second theorem applies this to the literal fixed subgroup
`C_(Z_lambda)(V_beta ∩ Q_alpha')` when that subgroup is trapped in Q_beta.
The fixed subgroup is then normal in the terminal local group and is exactly
the intersection of all neighboring centers, as well as its intersection
with any neighboring center whose core contains the original actor.
These are the graph-specific fixed-space steps in the noncentral branch of
DGS, *Groups and Graphs* (1985), 8.7, printed p.140. It does not assert
the fixed-centralizer escape or final centrality conclusion.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A beta-core actor fixing the opposite core intersection fixes the
whole beta span if that intersection has index below the moving unitary
field-square bound. The center estimates use the original moving edge. -/
theorem source_unitary_core_actor_fixed_of_small_index
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n) ∨
      IsSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n))
    (hsmall : (Q (family P) a').relIndex (V (family P) beta 1) < (2^n)^2)
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hEQ : E ≤ Q (family P) beta)
    (hEA : E ≤ centralizer ((V (family P) beta 1 ⊓ Q (family P) a' : Subgroup G) : Set G)) :
    E ≤ centralizer (V (family P) beta 1 : Set G) := by
  let := finite_endpoints h
  let F := family P
  let A := V F beta 1 ⊓ Q F a'
  have hVL : V F beta 1 ≤ stabilizer F beta :=
    V_le_stabilizer_of_dist_add_le_b F h.generate beta beta 1
      (by simpa only [SimpleGraph.dist_self,zero_add] using hb.le)
  let : Finite (V F beta 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
  have hupper : (centralizer (E : Set G)).relIndex (V F beta 1) ≤
      (Q F a').relIndex (V F beta 1) := by
    have hAC : A ≤ centralizer (E : Set G) := le_centralizer_iff.mp hEA
    have hh := relIndex_le_of_le_left hAC (A.subgroupOf (V F beta 1)).index_ne_zero_of_finite
    simpa only [A,inf_relIndex_left] using hh
  have heven : Even ((graph F).dist beta a') := by
    obtain ⟨k,hk⟩ := (source_critical_geometry h d hc hab hd hb hcomm).1
    refine ⟨k,?_⟩
    change (graph (family P)).dist beta a' = k+k
    omega
  have ht := (even_dist_iff F h.generate beta a').mp heven
  apply le_centralizer_iff.mp
  rw [V_one_eq_sup_neighbors]
  apply sup_le
  · exact (Z_centralizes_Q F beta (source_Z_Q_U h beta).1).trans (centralizer_le hEQ)
  · apply iSup_le
    intro z
    by_contra hz
    have hzt : z.val.type = w.val.type := by
      have hz' := z.property.1
      have hw' := w.property.1
      cases hzt : z.val.type <;> cases hwt : w.val.type <;>
        cases hbt : beta.type <;> cases het : a'.type <;> simp_all
    have hEL : E ≤ d.localGroup z.val := pGroup_le_localGroup F d z.val E
      (IsElementaryAbelian.isPGroup 2 E)
      (hEQ.trans ((source_Z_Q_U h beta).2.trans
        ((ballKernel_one_le_edge F z.property).trans inf_le_right)))
    have hEQz : ¬ E ≤ Q F z.val := by
      intro he
      exact hz ((Z_centralizes_Q F z.val (source_Z_Q_U h z.val).1).trans (centralizer_le he))
    have hl := source_moving_unitary_orbit_bound h hB d hc hab hd hb hcomm models
      w hm hn hu hzt E hEL hEQz
    have hi := relIndex_le_of_le_right (Z_neighbor_le_V F z.property)
      (((centralizer (E : Set G)).subgroupOf (V F beta 1)).index_ne_zero_of_finite)
    exact (not_le_of_gt hsmall) (hl.trans (hi.trans hupper))

/-- Under a trapping hypothesis, the literal moving-center fixed subgroup
already fixes V_beta. This discharges the graph-specific part of the
fixed-centralizer argument; only the displayed numerical comparison remains. -/
theorem source_unitary_trapped_fixed_centralizer
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n) ∨
      IsSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n))
    (hsmall : (Q (family P) a').relIndex (V (family P) beta 1) < (2^n)^2)
    (htrap : Z (family P) w.val ⊓ centralizer
      ((V (family P) beta 1 ⊓ Q (family P) a' : Subgroup G) : Set G) ≤ Q (family P) beta) :
    Z (family P) w.val ⊓ centralizer
      ((V (family P) beta 1 ⊓ Q (family P) a' : Subgroup G) : Set G) ≤
        centralizer (V (family P) beta 1 : Set G) := by
  let := CommutingOneProfile.source_center_elementary h w.val
  let C := Z (family P) w.val ⊓ centralizer
    ((V (family P) beta 1 ⊓ Q (family P) a' : Subgroup G) : Set G)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  exact source_unitary_core_actor_fixed_of_small_index h hB d hc hab hd hb hcomm models
    w hm hn hu hsmall C htrap inf_le_right

/-- A trapped moving-center fixed subgroup is normal in the terminal local
group and equals the whole neighboring-center intersection. The same group
is the intersection with any neighboring center whose core contains A. -/
theorem source_unitary_trapped_fixed_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n) ∨
      IsSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n))
    (hsmall : (Q (family P) a').relIndex (V (family P) beta 1) < (2^n)^2)
    (htrap : Z (family P) w.val ⊓ centralizer
      ((V (family P) beta 1 ⊓ Q (family P) a' : Subgroup G) : Set G) ≤ Q (family P) beta) :
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    let C := Z F w.val ⊓ centralizer (A : Set G)
    d.localGroup a' ≤ normalizer (C : Set G) ∧
      C = neighborCenterIntersection F a' ∧
      ∀ z : (graph F).neighborSet a', A ≤ Q F z.val → C = Z F w.val ⊓ Z F z.val := by
  let := finite_endpoints h
  let F := family P
  let A := V F beta 1 ⊓ Q F a'
  let C := Z F w.val ⊓ centralizer (A : Set G)
  change d.localGroup a' ≤ normalizer (C : Set G) ∧
    C = neighborCenterIntersection F a' ∧
    ∀ z : (graph F).neighborSet a', A ≤ Q F z.val → C = Z F w.val ⊓ Z F z.val
  have hCV : C ≤ centralizer (V F beta 1 : Set G) :=
    source_unitary_trapped_fixed_centralizer h hB d hc hab hd hb hcomm models
      w hm hn hu hsmall htrap
  obtain ⟨T,hT⟩ := source_moving_edge_generation h hB d hc hab hd hb hcomm (models a') w hm
  let T₀ := (T : Subgroup ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup G)).map
    (stabilizer F a' ⊓ stabilizer F w.val).subtype
  change V F beta 1 ⊔ T₀ = d.localGroup a' at hT
  have hTw : T₀ ≤ stabilizer F w.val := (map_subtype_le _).trans inf_le_right
  have hTA : ⁅T₀,A⁆ ≤ Q F w.val :=
    source_moving_actor_displacement h d hc hab hd hb hcomm w (models w.val) T
  have hTC : T₀ ≤ normalizer (C : Set G) :=
    normalizes_inf_centralizer_of_displacement T₀ (Z F w.val) A (Q F w.val)
      (hTw.trans (stabilizer_normalizes_Z F w.val))
      (hTw.trans (stabilizer_normalizes_Q F w.val))
      (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1)
      (by rw [commutator_comm]; exact hTA)
  have hMC : d.localGroup a' ≤ normalizer (C : Set G) := by
    rw [←hT]
    exact sup_le ((le_centralizer_iff.mp hCV).trans (Subgroup.centralizer_le_normalizer _)) hTC
  have hCZ (z : (graph F).neighborSet a') : C ≤ Z F z.val := by
    obtain ⟨g,hg,hgz⟩ := d.transitive a' w z
    have he : (Z F w.val).map (MulAut.conj g).toMonoidHom = Z F z.val :=
      (Z_translate F g w.val).symm.trans (congrArg (Z F) hgz)
    rw [←he]
    exact normal_subgroup_le_conjugate (d.localGroup a') C (Z F w.val) hMC inf_le_left hg
  have hCX : C ≤ neighborCenterIntersection F a' :=
    le_iInf (fun z : (graph F).neighborSet a' => hCZ z)
  have hpair (z : (graph F).neighborSet a') (hAz : A ≤ Q F z.val) :
      C = Z F w.val ⊓ Z F z.val := by
    apply le_antisymm (le_inf inf_le_left (hCZ z))
    exact le_inf inf_le_left (inf_le_right.trans
      ((Z_centralizes_Q F z.val (source_Z_Q_U h z.val).1).trans (centralizer_le hAz)))
  obtain ⟨_,_,_,_,prev,hp,_,hVP,_⟩ := source_critical_geometry h d hc hab hd hb hcomm
  have hXpair : neighborCenterIntersection F a' ≤ Z F w.val ⊓ Z F prev :=
    le_inf (iInf_le (fun z : (graph F).neighborSet a' => Z F z.val) w)
      (iInf_le (fun z : (graph F).neighborSet a' => Z F z.val) ⟨prev,hp⟩)
  refine ⟨hMC,le_antisymm hCX ?_,hpair⟩
  rw [hpair ⟨prev,hp⟩ (inf_le_left.trans hVP)]
  exact hXpair

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

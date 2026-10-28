module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.PathControl

/-!
# The shifted noncommuting critical pair at b=2

The literal noncentral condition on the middle local group excludes the
central branch of 6.2(c) throughout its vertex orbit. If a predecessor
center were trapped in the opposite stabilizer, the 7.1 Sylow product
would contain it. Its product with the starting center would then be
normal in that full stabilizer, contradicting the earlier 6.5 obstruction
via the correctly oriented 6.6 argument. A two-step distance calculation
and the centralizer Sylow produce the shifted noncommuting critical pair.
Local edge maximality constructs a suitable predecessor.

This proves the b=2 assertion of DGS 10.3 from the genuine earlier 7.1
Sylow product and 6.5 normality obstruction. It uses the intrinsic source
local group, both vertex orbits, the actual critical minimum and the full
permutation kernel. It neither identifies that kernel with Q nor assumes
a tree. The D identities and 10.6/10.9/10.10 remain separate obligations.
Source: DGS, *Groups and Graphs* (1985), 10.3, printed pp.154--155,
using 6.2(c,d), 6.5, 6.6 and 7.1.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P

private theorem shifted_core_normalized (v : Vertex F) :
    stabilizer F v ≤ normalizer (Q F v : Set G) :=
  (stabilizer F v).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

private theorem shifted_core_adjacent (h : LocallyRankOneTriple P B)
    {v w : Vertex F} (he : (graph F).Adj v w) : Q F v ≤ stabilizer F w :=
  (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F he).trans inf_le_right)

/-- The opposite endpoint's centralizer Sylow and the earlier 6.5 obstruction
exclude normality of the adjacent center product, with the source orientation. -/
theorem bTwo_center_product_obstruction (h : LocallyRankOneTriple P B)
    {t v : Vertex F} (htv : (graph F).Adj t v)
    (hCS : Stellmacher.IsSylowSubgroupIn (Q F t)
      (stabilizer F t ⊓ centralizer (Z F t : Set G)))
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F t ⊓ Q F v : Subgroup G) : Set G)) :
    ¬ stabilizer F v ≤ normalizer ((Z F t ⊔ Z F v : Subgroup G) : Set G) := by
  intro hn
  have hi := inf_centralizer_eq_inf_core (stabilizer F t) (Q F t) (Z F t)
    (Q F v) (isPGroup_pCoreIn 2 _) (shifted_core_adjacent h htv.symm)
    (Q_le_stabilizer F t) (graph_Q_centralizes_Z h t) (shifted_core_normalized t) hCS
  have he : Q F v ⊓ centralizer (Z F t : Set G) =
      Q F v ⊓ centralizer ((Z F t ⊔ Z F v : Subgroup G) : Set G) := by
    apply le_antisymm
    · apply le_inf inf_le_left
      rw [le_centralizer_iff]
      exact sup_le (le_centralizer_iff.mp inf_le_right)
        ((le_centralizer_iff.mp (graph_Q_centralizes_Z h v)).trans
          (centralizer_le inf_le_left))
    · exact inf_le_inf_left _ (centralizer_le (show Z F t ≤ Z F t ⊔ Z F v from le_sup_left))
  apply hnot
  rw [inf_comm, ←hi, he]
  exact (le_inf (shifted_core_normalized v)
    (hn.trans (normalizer_le_normalizer_centralizer _))).trans
    inf_normalizer_le_normalizer_inf

/-- The escape assertion in 10.3. A trapped neighbor center lies in the
critical Sylow product, making its product with the starting center normal. -/
theorem bTwo_neighbor_center_escape (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x)) (hb : b F = 2)
    {t v w : Vertex F} (htv : (graph F).Adj t v) (hc : IsCriticalPair F v w)
    (hs : Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w))
    (hgen : Z F w ⊔ (stabilizer F v ⊓ stabilizer F t) = stabilizer F v)
    (hCS : Stellmacher.IsSylowSubgroupIn (Q F t)
      (stabilizer F t ⊓ centralizer (Z F t : Set G)))
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F t ⊓ Q F v : Subgroup G) : Set G)) :
    ¬ Z F t ≤ stabilizer F w := by
  let := finite_endpoints h
  have hZQ : Z F v ≤ Q F v := fun z hz =>
    ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hz)).1
  have htQ : Z F t ≤ Q F v := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr htv,hb]; decide)
  have hnZ (x : Vertex F) : stabilizer F x ≤ normalizer (Z F x : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F x)).mp (Z_normal F x)
  have hvw := Z_le_stabilizer_of_dist_le_b F h.generate v w hc.1.le
  have hwv := (criticalPair_centers F h.generate hc).1
  have he := source_radius_escape_of_product_obstruction
    (stabilizer F w) (stabilizer F v) (stabilizer F t)
    (Z F v) (Z F w) (Z F t) (Z F t ⊔ Z F v)
    ((isPGroup_pCoreIn 2 (stabilizer F v)).to_le (sup_le htQ hZQ))
    ((sup_le htQ hZQ).trans ((Q_le_stabilizer F v).trans (hnZ v))) le_sup_right
    (hvw.trans (hnZ w)) (hwv.trans (hnZ v)) (graph_Q_centralizes_Z h w)
    hs le_sup_left hgen (hnZ v) (hnZ t)
    (bTwo_center_product_obstruction h htv hCS hnot)
  intro ht
  exact he (sup_le ht hvw)

/-- The shifted pair in 10.3 is critical in both orders and still has
noncommuting centers. Its distance is the actual two-orbit minimum. -/
theorem bTwo_shifted_critical_pair (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x)) (hb : b F = 2)
    {t v m w : Vertex F} (htv : (graph F).Adj t v)
    (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w)
    (hc : IsCriticalPair F v w)
    (hs : Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w))
    (hgen : Z F w ⊔ (stabilizer F v ⊓ stabilizer F t) = stabilizer F v)
    (hCSt : Stellmacher.IsSylowSubgroupIn (Q F t)
      (stabilizer F t ⊓ centralizer (Z F t : Set G)))
    (hCSm : Stellmacher.IsSylowSubgroupIn (Q F m)
      (stabilizer F m ⊓ centralizer (Z F m : Set G)))
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F t ⊓ Q F v : Subgroup G) : Set G)) :
    ¬ Z F t ≤ stabilizer F w ∧ IsCriticalPair F t m ∧
      IsCriticalPair F m t ∧ ⁅Z F m,Z F t⁆ ≠ ⊥ := by
  let := finite_endpoints h
  have hescape := bTwo_neighbor_center_escape h hS hb htv hc hs hgen hCSt hnot
  have hdist : (graph F).dist t m ≤ b F := by
    have hd := (connected_graph h).dist_triangle (u := t) (v := v) (w := m)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr htv,
      SimpleGraph.dist_eq_one_iff_adj.mpr hvm, hb] at *
    exact hd
  let := graph_Z_elementary h t
  have htM : Z F t ≤ stabilizer F m := Z_le_stabilizer_of_dist_le_b F h.generate t m hdist
  have hi := inf_centralizer_eq_inf_core (stabilizer F m) (Q F m) (Z F m)
    (Z F t) (IsElementaryAbelian.isPGroup 2 _) htM (Q_le_stabilizer F m)
    (graph_Q_centralizes_Z h m) (shifted_core_normalized m) hCSm
  have hne : ⁅Z F t,Z F m⁆ ≠ ⊥ := by
    intro he
    have htC := commutator_eq_bot_iff_le_centralizer.mp he
    have htQ : Z F t ≤ Q F m := by
      rw [inf_of_le_left htC] at hi
      exact hi.le.trans inf_le_right
    exact hescape (htQ.trans (shifted_core_adjacent h hmw))
  have hc' := graph_critical_of_noncommuting h hS hdist hne
  exact ⟨hescape,hc',graph_criticalPair_reverse h hS hc' hne,
    by rwa [commutator_comm]⟩

/-- Local maximality chooses the shifted neighbor. No shifted critical pair
or second noncommutation is included in the premises. -/
theorem bTwo_exists_shifted_critical_pair (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x)) (hb : b F = 2)
    {v m w : Vertex F} (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w)
    (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hs : Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w))
    (hCS : ∀ t, t.type = m.type → Stellmacher.IsSylowSubgroupIn (Q F t)
      (stabilizer F t ⊓ centralizer (Z F t : Set G)))
    (hnot : ∀ t, (graph F).Adj t v →
      ¬ stabilizer F v ≤ normalizer ((Q F t ⊓ Q F v : Subgroup G) : Set G)) :
    ∃ t, (graph F).Adj t v ∧ t ≠ m ∧
      Z F w ⊔ (stabilizer F v ⊓ stabilizer F t) = stabilizer F v ∧
      ¬ Z F t ≤ stabilizer F w ∧ IsCriticalPair F t m ∧
      IsCriticalPair F m t ∧ ⁅Z F m,Z F t⁆ ≠ ⊥ := by
  obtain ⟨t,ht,hgen⟩ := graph_exists_generating_neighbor h hS hc hne
    (fun _ he => graph_edge_isCoatom h he)
  have htype : t.type = m.type := by
    have h₀ := ht.1
    have h₁ := hvm.1
    cases hv : v.type <;> cases ht' : t.type <;> cases hm : m.type <;> simp_all
  have hh := bTwo_shifted_critical_pair h hS hb ht.symm hvm hmw hc hs hgen
    (hCS t htype) (hCS m rfl) (hnot t ht.symm)
  refine ⟨t,ht.symm,?_,hgen,hh⟩
  intro he
  subst t
  exact hh.1 ((graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hmw,hb]; decide)).trans
      (Q_le_stabilizer F w))

/-- Noncentrality in the actual source local group excludes the central
alternative of 6.2(c) throughout the same vertex orbit. -/
theorem bTwo_centralizer_sylow_of_noncentral (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {m : Vertex F} (hnc : ¬ Z F m ≤ centerIn (graphLocalGroup F m))
    {t : Vertex F} (ht : t.type = m.type) :
    Stellmacher.IsSylowSubgroupIn (Q F t)
      (stabilizer F t ⊓ centralizer (Z F t : Set G)) := by
  let := finite_endpoints h
  apply (graphLocalGroup_sylow_or_center h hB hSyl t).resolve_right
  intro he
  obtain ⟨g,rfl⟩ := (same_orbit_iff F t m).mpr ht
  apply hnc
  rw [Z_translate,graphLocalGroup_conjugate h,he,
    NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective]
  intro x hx
  exact ⟨((mem_omegaCenterIn_iff _ _).mp hx).1,
    ((mem_omegaCenterIn_iff _ _).mp hx).2.1⟩

/-- Source 10.3 at b=2 from noncentrality in the literal local group.
The only earlier theorem inputs are the 7.1 Sylow product and the 6.5
adjacent-core obstruction; the shifted pair and its movement are constructed. -/
theorem bTwo_shifted_pair_of_noncentral (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w : Vertex F}
    (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w)
    (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hnc : ¬ Z F m ≤ centerIn (graphLocalGroup F m))
    (hs : Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w))
    (hnot : ∀ t, (graph F).Adj t v →
      ¬ stabilizer F v ≤ normalizer ((Q F t ⊓ Q F v : Subgroup G) : Set G)) :
    ∃ t, (graph F).Adj t v ∧ t ≠ m ∧
      Z F w ⊔ (stabilizer F v ⊓ stabilizer F t) = stabilizer F v ∧
      ¬ Z F t ≤ stabilizer F w ∧ IsCriticalPair F t m ∧
      IsCriticalPair F m t ∧ ⁅Z F m,Z F t⁆ ≠ ⊥ := by
  exact bTwo_exists_shifted_critical_pair h (source_kernel_sylow h hB hSyl) hb
    hvm hmw hc hne hs (fun _ ht => bTwo_centralizer_sylow_of_noncentral h hB hSyl hnc ht) hnot

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

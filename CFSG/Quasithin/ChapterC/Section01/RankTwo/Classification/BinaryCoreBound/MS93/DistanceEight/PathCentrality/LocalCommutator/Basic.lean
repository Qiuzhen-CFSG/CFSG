module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Generation

/-!
# The local span and small displacement in MS93 (4.4.1)

The supplied common facts contain the marked natural structure. The proved
critical-module calculations supply the remaining fields of ModuleFacts;
no unfinished Section Three constructor is used.

The local orbit span contains the central Z-layer by transitivity on the
common edge, and lies in both endpoint kernels when b > 4. The common edge
also bounds [Z_a,Q_c] by its edge displacement, hence by the actual natural
subgroup U_a, with order at most four. These are preparations for the two
branches of (4.4.1), not proofs of its commutator conclusions.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), printed pp.890--892, and the notation on p.881.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

/-- The literal natural structure already present in the supplied common facts. -/
def naturalStructure (common : CommonFacts R source geometry) : BinaryNaturalStructure source where
  X_eq_Z := common.X_eq_Z
  natural := common.natural
  decomposition := common.decomposition
  disjoint := common.disjoint

/-- Assemble all earlier module facts using the proved critical-module results. -/
def moduleFacts [Finite M] (common : CommonFacts R source geometry) : ModuleFacts source geometry where
  X_eq_Z := common.X_eq_Z
  natural := common.natural
  full_commutation := common.full_commutation
  decomposition := common.decomposition
  disjoint := common.disjoint
  critical_U_index := (naturalStructure common).critical_U_index geometry common.large_distance
  critical_Z_commutator_card :=
    (naturalStructure common).critical_Z_commutator_card geometry common.large_distance
  b_four_class_two := (naturalStructure common).b_four_class_two geometry

/-- Identify the orbit definition with the existing relative normal-closure API. -/
theorem span_eq_conjugates (a c : Vertex R) :
    localZSpan R a c = NormalizerTransfer.conjugatesIn (Z R a) (stabilizer R c) :=
  localZSpan_eq_conjugates R a c

/-- The denominator in the source quotient W/Z_c actually belongs to W. -/
theorem center_Z_le_span [Finite M] {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) : Z R c ≤ localZSpan R a c := by
  rw [span_eq_conjugates]
  exact Escape.Initial.Natural.Z_le_conjugatesIn_of_dist_two c a hc
    (by rw [SimpleGraph.dist_comm]; exact hd)

/-- At distance two the whole span lies in both kernels when b > 4. -/
theorem span_le_kernel_intersection {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 4 < geometry.b R) :
    localZSpan R a c ≤ Q R a ⊓ Q R c := by
  apply le_inf
  · apply (localZSpan_le_V R hd.le).trans
    apply V_le_Q_of_dist_add_two_lt R hc
    rw [SimpleGraph.dist_comm, hd]
    exact hb
  · exact localZSpan_le_Q R hc hd.le (by omega)

/-- Every displacement stays inside the elementary local span. This does not
assert its containment in the fixed core. -/
theorem span_commutator_le_span (a c : Vertex R) :
    ⁅localZSpan R a c, Q R c⁆ ≤ localZSpan R a c :=
  le_normalizer_iff_commutator_le_left.mp
    ((show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans
      (localZSpan_normalized R a c))

/-- Commuting the local span with Q_c is the local closure of the initial
small displacement, with the same stabilizer and conjugation convention. -/
theorem span_commutator_eq_conjugates {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2) (hb : 2 < geometry.b R) :
    ⁅localZSpan R a c, Q R c⁆ =
      NormalizerTransfer.conjugatesIn ⁅Z R a, Q R c⁆ (stabilizer R c) := by
  have hW : localZSpan R a c ≤ Q R c := localZSpan_le_Q R hc hd hb
  rw [localZSpan, NormalizerTransfer.conjugatesIn, commutator_iSup_of_le]
  · apply iSup_congr
    intro g
    have hQ : (Q R c).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom = Q R c :=
      mem_normalizer_iff_map_conj_eq.mp
        (Q_normalized R c ((stabilizer R c).inv_mem g.property))
    rw [NormalizerTransfer.rightConjugate, map_commutator, hQ, Z_act]
  · intro g
    exact (le_iSup (fun k : stabilizer R c =>
      Z R (Stellmacher.PushingUp.AmalgamGraph.act R k a)) g).trans hW

/-- The initial displacement detects fixedness of the entire local span. -/
theorem span_commutator_le_fixed_iff {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2) (hb : 2 < geometry.b R) :
    ⁅localZSpan R a c, Q R c⁆ ≤ fixedCore R c ↔
      ⁅Z R a, Q R c⁆ ≤ fixedCore R c := by
  constructor
  · intro h
    exact (commutator_mono (Z_le_localZSpan R a c) le_rfl).trans h
  · intro h
    rw [span_commutator_eq_conjugates hc hd hb]
    apply iSup_le
    intro g
    change (⁅Z R a, Q R c⁆).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom ≤ _
    have hD : (fixedCore R c).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom =
        fixedCore R c := mem_normalizer_iff_map_conj_eq.mp
      (PathCentrality.fixedCore_normalized R c ((stabilizer R c).inv_mem g.property))
    exact (map_mono h).trans hD.le

/-- The actual two-step displacement lies in the natural subgroup at its origin. -/
theorem displacement_le_U [Finite M] (common : CommonFacts R source geometry)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) : ⁅Z R a, Q R c⁆ ≤ U R a := by
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two R a c hd
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hat
    cases hcol : color R t <;> simp_all
  have hQc : Q R c ≤ Q R t := Q_le_adjacent_h R ht hct
  exact (commutator_mono le_rfl hQc).trans
    (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) a t ha hat)

/-- The q² bound used on p.890, proved on the actual commutator subgroup. -/
theorem displacement_card_le_four [Finite M] (common : CommonFacts R source geometry)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) :
    Nat.card (⁅Z R a, Q R c⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two R a c hd
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hat
    cases hcol : color R t <;> simp_all
  have hle : ⁅Z R a, Q R c⁆ ≤ ⁅Z R a, Q R t⁆ :=
    commutator_mono le_rfl (Q_le_adjacent_h R ht hct)
  let := finite_stabilizer R a
  let : Finite (⁅Z R a, Q R t⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective
      (inclusion ((Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
        (moduleFacts common) a t ha hat).trans ((U_le_Z R a).trans (Z_le_stabilizer R a))))
      (inclusion_injective _)
  exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)).trans
    (Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
      (moduleFacts common) a t ha hat)

/-- The noncontainment in (4.4.1) supplies a genuine moving element of Z_a. -/
theorem exists_moving_generator {a c : Vertex R}
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c) :
    ∃ x ∈ Z R a, ¬ ⁅zpowers x, Q R c⁆ ≤ fixedCore R c := by
  classical
  by_contra! h
  apply hn
  apply commutator_le.mpr
  intro x hx y hy
  exact h x hx (commutator_mem_commutator (mem_zpowers x) hy)

/-- Failure of fixedness of W is already witnessed by one actual element of Q_c. -/
theorem exists_moving_actor {a c : Vertex R}
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c) :
    ∃ x ∈ Q R c, ¬ ⁅localZSpan R a c, zpowers x⁆ ≤ fixedCore R c := by
  classical
  by_contra! h
  apply hn
  apply commutator_le.mpr
  intro z hz x hx
  exact h x hx (commutator_mem_commutator (Z_le_localZSpan R a c hz) (mem_zpowers x))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator

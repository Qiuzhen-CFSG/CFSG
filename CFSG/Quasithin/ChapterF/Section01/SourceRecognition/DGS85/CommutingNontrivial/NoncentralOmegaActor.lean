module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathOmegaActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.DistanceSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.EscapeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration

/-!
# The noncentral opposite omega actor in DGS 8.7

The path actor argument in 8.7 only needs the middle rank-one quotient to be
non-dihedral.  A supplied non-dihedral marking at the starting vertex moves to
the middle predecessor by the literal same-type quotient transport.  The
reciprocal escape then supplies the escaping terminal actor, and the path
normalizer identifies its quotient image with the whole beta omega-center.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
8.5--8.7, printed pp.139--140.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
universe u
variable {G : Type u} [Group G]

variable {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "Γ" => Reduction.reducedFamily L S₀

private theorem reduced_non_dihedral_of_same_type
    (h : HypothesisF11 L S₀) {v w : Vertex Γ}
    (ht : v.type = w.type)
    (hnd : ¬ Nonempty ((graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)) ≃*
      DihedralGroup 5)) :
    ¬ Nonempty ((graphLocalGroup Γ w ⧸ pCore 2 (graphLocalGroup Γ w)) ≃*
      DihedralGroup 5) := by
  obtain ⟨g, hg⟩ := (same_orbit_iff Γ v w).mpr ht
  obtain ⟨_, f, _, _, _⟩ := local_quotient_parameter_transport
    (Reduction.reduced_triple h) g hg
  intro hw
  obtain ⟨ew⟩ := hw
  exact hnd ⟨f.trans ew⟩

/-- In the noncentral branch, a non-dihedral starting type makes the full
opposite actor equal to the actual beta quotient-Sylow omega-center order.
No naturality or commuting-intersection premise is used. -/
theorem reduced_noncentral_opposite_omega_index
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a, Z Γ a'⁆ = ⊥)
    (hne : ⁅V Γ beta 1 ⊓ Q Γ a', V Γ a' 1⁆ ≠ ⊥)
    (hnd : ¬ Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃*
      DihedralGroup 5)) :
    ∃ R : Sylow 2 (graphLocalGroup Γ beta),
      (Q Γ beta).relIndex (V Γ a' 1) = Nat.card (omegaCenterIn
        ((R : Subgroup (graphLocalGroup Γ beta)).map
          (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hb3 := reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne
  obtain ⟨_, _, _, _, mid, ham, hdm, _, _⟩ :=
    source_critical_geometry ht d hc hab hd hb hcomm
  change (graph Γ).dist beta mid + 1 = (graph Γ).dist beta a' at hdm
  change (graph Γ).Adj a' mid at ham
  have hdist : (graph Γ).dist beta a' = 2 := by omega
  have hbm : (graph Γ).Adj beta mid :=
    SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  have hba : beta ≠ a' := by
    intro he
    rw [he, SimpleGraph.dist_self] at hdist
    omega
  have hat : a.type = mid.type :=
    (Bool.eq_not_of_ne hab.1).trans (Bool.eq_not_of_ne hbm.1.symm).symm
  have hndmid := reduced_non_dihedral_of_same_type h hat hnd
  have hAQ : V Γ a' 1 ≤ Q Γ mid := V_le_Q_of_dist_add_lt_b Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) a' mid 1
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr ham]; omega) (d.kernel_sylow mid)
  have hAL : V Γ a' 1 ≤ d.localGroup beta := by
    apply neighbor_le_graphLocalGroup ht (Reduction.reduced_kernel_sylow h) a' beta hb
    change (graph Γ).dist a' beta + 1 ≤ b Γ
    simpa only [SimpleGraph.dist_comm] using hd.le
  let : IsElementaryAbelian 2 (V Γ a' 1) := V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow a' (by omega)
  have hesc := reduced_reciprocal_escape h (Reduction.reduced_graph_core_obstruction h)
    models hc hab hd hb hcomm hne
  obtain ⟨R, hR⟩ := source_path_normalized_omega_image ht
    (Reduction.reduced_borel_core_sylow h) d hbm ham hba
    (models beta) (models mid) hndmid (V Γ a' 1) hAL hAQ hesc
    (stabilizer_normalizes_V Γ a' 1)
  refine ⟨R, ?_⟩
  have hi := BinaryConjugationSection.actor_image_card_eq_relIndex
    (d.localGroup beta) (Q Γ beta) (V Γ a' 1)
    (QuotientGroup.mk' (pCore 2 (d.localGroup beta)))
    (local_quotient_kernel Γ d beta (MulEquiv.refl _)) hAL
  rw [hR] at hi
  exact hi.symm

/-! The existential Sylow supplied by the path actor can be replaced by any
quotient Sylow at beta.  This is the literal parameter-invariance statement
used when a consumer has already fixed its original local Sylow. -/
theorem reduced_noncentral_opposite_omega_index_of
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a, Z Γ a'⁆ = ⊥)
    (hne : ⁅V Γ beta 1 ⊓ Q Γ a', V Γ a' 1⁆ ≠ ⊥)
    (hnd : ¬ Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃*
      DihedralGroup 5))
    (Rβ : Sylow 2 (graphLocalGroup Γ beta)) :
    (Q Γ beta).relIndex (V Γ a' 1) = Nat.card (omegaCenterIn
      ((Rβ : Subgroup (graphLocalGroup Γ beta)).map
        (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))) := by
  obtain ⟨R, hR⟩ := reduced_noncentral_opposite_omega_index h models hc hab hd hb hcomm hne hnd
  let ht := Reduction.reduced_triple h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : ∀ i, Finite (graphLocalGroup Γ i) := fun v =>
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let Rq := R.mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ beta)))
  let Rβq := Rβ.mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ beta)))
  obtain ⟨_, _, _, _, hq⟩ := local_quotient_parameter_transport ht
    (1 : Reduction.G₀ L S₀)
    (show (1 : Reduction.G₀ L S₀) • beta = beta from one_smul _ beta)
  have hparam := hq Rq Rβq
  apply hR.trans
  convert hparam using 1 <;> rfl

/-! Same-type transport of the literal quotient parameter along the terminal
neighborhood.  This is the source `q_lambda = q_alpha` comparison. -/
theorem reduced_critical_neighbor_quotient_omega_card
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a, Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (Tα : Sylow 2 (graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)))
    (Tlambda : Sylow 2 (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val))) :
    Nat.card (omegaCenterIn (Tα : Subgroup
      (graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)))) =
      Nat.card (omegaCenterIn (Tlambda : Subgroup
        (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)))) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hoddB := (source_critical_geometry ht d hc hab hd hb hcomm).1
  have hodd : Odd ((graph Γ).dist a a') := by
    rw [hc.1]
    exact hoddB
  have hna : a.type ≠ a'.type := (odd_dist_iff Γ ht.generate a a').mp hodd
  have hwa : a.type = w.val.type := by
    have hn := w.property.1
    cases hat : a.type <;> cases hwt : w.val.type <;> cases het : a'.type <;> simp_all
  obtain ⟨g, hg⟩ := (same_orbit_iff Γ a w.val).mpr hwa
  obtain ⟨_, _, _, _, hq⟩ := local_quotient_parameter_transport ht g hg
  exact hq Tα Tlambda

/-! The terminal and beta quotient parameters are identified by the actual
same-type conjugation in the reduced critical configuration. -/
theorem reduced_critical_terminal_quotient_omega_card
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a, Z Γ a'⁆ = ⊥)
    (T' : Sylow 2 (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')))
    (Tβ : Sylow 2 (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta))) :
    Nat.card (omegaCenterIn (T' : Subgroup
      (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')))) =
      Nat.card (omegaCenterIn (Tβ : Subgroup
        (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)))) := by
  obtain ⟨_, _, _, _, _, _, hparam⟩ :=
    reduced_critical_parameter_transport h hc hab hd hb hcomm
  exact hparam T' Tβ

/-! The chosen moving-neighbor form is useful when the consumer already carries
the special/projective unitary marking at that neighbor.  The marking is
retained as an explicit argument so this wrapper can be applied directly to
the moving-unitary rows; the actor equality itself is independent of which
unitary cover is used. -/
theorem reduced_noncentral_moving_unitary_opposite_omega_index
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a, Z Γ a'⁆ = ⊥)
    (hne : ⁅V Γ beta 1 ⊓ Q Γ a', V Γ a' 1⁆ ≠ ⊥)
    (hnd : ¬ Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃*
      DihedralGroup 5))
    (_w : (graph Γ).neighborSet a')
    (_hm : ⁅V Γ beta 1 ⊓ Q Γ a', Z Γ _w.val⁆ ≠ ⊥)
    {n : ℕ}
    (_hu : ClassicalGroup.IsPSU (graphLocalGroup Γ _w.val ⧸
      pCore 2 (graphLocalGroup Γ _w.val)) 3 (2 ^ n) ∨
      IsSU (graphLocalGroup Γ _w.val ⧸
        pCore 2 (graphLocalGroup Γ _w.val)) 3 (2 ^ n)) :
    ∃ R : Sylow 2 (graphLocalGroup Γ beta),
      (Q Γ beta).relIndex (V Γ a' 1) = Nat.card (omegaCenterIn
        ((R : Subgroup (graphLocalGroup Γ beta)).map
          (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))) := by
  exact reduced_noncentral_opposite_omega_index h models hc hab hd hb hcomm hne hnd

/-! Variant with the actual chosen moving neighbor and its unitary quotient
marking retained in the source interface. -/
theorem reduced_noncentral_chosen_moving_unitary_opposite_omega_index
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a, Z Γ a'⁆ = ⊥)
    (hne : ⁅V Γ beta 1 ⊓ Q Γ a', V Γ a' 1⁆ ≠ ⊥)
    (hnd : ¬ Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃*
      DihedralGroup 5))
    (_w : (graph Γ).neighborSet a')
    (_hm : ⁅V Γ beta 1 ⊓ Q Γ a', Z Γ _w.val⁆ ≠ ⊥)
    {n : ℕ}
    (_hu : ClassicalGroup.IsPSU (graphLocalGroup Γ _w.val ⧸
      pCore 2 (graphLocalGroup Γ _w.val)) 3 (2 ^ n) ∨
      IsSU (graphLocalGroup Γ _w.val ⧸
        pCore 2 (graphLocalGroup Γ _w.val)) 3 (2 ^ n)) :
    ∃ R : Sylow 2 (graphLocalGroup Γ beta),
      (Q Γ beta).relIndex (V Γ a' 1) = Nat.card (omegaCenterIn
        ((R : Subgroup (graphLocalGroup Γ beta)).map
          (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))) := by
  exact reduced_noncentral_moving_unitary_opposite_omega_index h models hc hab hd hb hcomm hne hnd
    _w _hm _hu

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

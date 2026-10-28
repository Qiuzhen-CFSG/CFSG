module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NeighborSeparation

/-!
# Central intersections and the remaining Chapter 11 layer

At a cubic beta vertex, the two neighboring centers centralize the mixed
core-center intersection. Their transitivity identifies this intersection
with the intersection of the centers. On the A₅ branch the opposite-seed
Sylow supplement then identifies it with Zβ, without assuming Qα = Zα.

For Z₀ = (intersection of neighboring cores at beta) intersect Q at another
beta vertex, the mixed intersection identity makes Z₀ Zα normal in the
alpha stabilizer. Its commutator with Qα lies in Z₀, and the two transitive
normalizers force that commutator to vanish in the faithful graph. The
actual edge Sylow then puts the elementary Z₀ inside Zβ. Vanishing of Z₀
is a further source step, not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.6), printed pp.172--173. `MixedCentralLayers` supplies the original
mixed-pair consumer with its literal reduced graph and quotient maps.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The first mixed core-center intersection equals the intersection of centers. -/
theorem source_cubic_center_inf_core (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3) :
    Z (family P) a ⊓ Q (family P) c = Z (family P) a ⊓ Z (family P) c := by
  let := finite_endpoints h
  have hcentral : Z (family P) a ⊔ Z (family P) c ≤
      centralizer (Z (family P) a ⊓ Q (family P) c : Set G) := by
    apply sup_le
    · exact (le_centralizer_iff.mp (source_core_centralizes_center h a)).trans
        (centralizer_le (inf_le_left.trans ((source_Z_Q_U h a).1.trans (map_subtype_le _))))
    · exact (le_centralizer_iff.mp (source_core_centralizes_center h c)).trans
        (centralizer_le inf_le_right)
  obtain ⟨g,hg,hga⟩ := source_cubic_center_pair_transitive h hc hb hbc hac hcard c hbc
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1,?_⟩
    have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom hx.1
    rw [←Z_translate,hga] at hm
    have hh := (mem_centralizer_iff.mp (hcentral hg)) x hx
    change g * x * g⁻¹ ∈ Z (family P) c at hm
    change x ∈ Z (family P) c
    simpa only [←hh,mul_inv_cancel_right] using hm
  · exact inf_le_inf_left _ ((source_Z_Q_U h c).1.trans (map_subtype_le _))


private theorem elementary_central_edge_le_center (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)
    (hC : A ≤ centralizer ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 : Set G)) :
    A ≤ Z (family P) b := by
  let := finite_endpoints h
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hab.symm
  have he := sylow_image_eq_edge_core (stabilizer (family P) b)
    (stabilizer (family P) b ⊓ stabilizer (family P) a) inf_le_left
    (source_edge_core_sylow h hB hab.symm) T hT
  rw [inf_comm] at he
  have ho : A ≤ omegaCenterIn ((T : Subgroup (stabilizer (family P) b)).map
      (stabilizer (family P) b).subtype) := by
    rw [he]
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨hA hx,hC hx,elemPow_eq_one_of_isElementaryAbelian x hx⟩
  exact ho.trans (le_iSup (fun R : Sylow 2 (stabilizer (family P) b) =>
    omegaCenterIn ((R : Subgroup (stabilizer (family P) b)).map
      (stabilizer (family P) b).subtype)) T)

/-- The two neighboring centers intersect in the actual beta center. -/
theorem source_cubic_a5_center_intersection (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5)) :
    Z (family P) a ⊓ Z (family P) c = Z (family P) b := by
  let := source_center_elementary h a
  let A := Z (family P) a ⊓ Z (family P) c
  let : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  have he := source_cubic_a5_edge_core_eq_seed_sup_core h hB hS hc hb hbc hac hcard e
  apply le_antisymm
  · apply elementary_central_edge_le_center h hB hS hab A
    · rw [he]
      exact inf_le_left.trans (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans le_sup_right)
    · rw [he]
      apply le_centralizer_iff.mpr
      apply sup_le
      · exact inf_le_left.trans ((le_centralizer_iff.mp (source_core_centralizes_center h c)).trans
          (centralizer_le (inf_le_right.trans ((source_Z_Q_U h c).1.trans (map_subtype_le _)))))
      · exact (source_core_centralizes_center h a).trans (centralizer_le inf_le_left)
  · exact le_inf (source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm)
      (source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hbc)

/-- The mixed core-center intersection is Zβ, without Qα = Zα. -/
theorem source_cubic_a5_center_inf_core_eq (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5)) :
    Z (family P) a ⊓ Q (family P) c = Z (family P) b :=
  (source_cubic_center_inf_core h hc hb hbc hac hcard).trans
    (source_cubic_a5_center_intersection h hB hS hc hb hcomm hbc hac hcard e)


/-- The mixed intersection in the other order has the same center intersection. -/
theorem source_cubic_core_inf_center (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3) :
    Q (family P) a ⊓ Z (family P) c = Z (family P) a ⊓ Z (family P) c := by
  let := finite_endpoints h
  have hcentral : Z (family P) a ⊔ Z (family P) c ≤
      centralizer (Q (family P) a ⊓ Z (family P) c : Set G) := by
    apply sup_le
    · exact (le_centralizer_iff.mp (source_core_centralizes_center h a)).trans
        (centralizer_le inf_le_left)
    · exact (le_centralizer_iff.mp (source_core_centralizes_center h c)).trans
        (centralizer_le (inf_le_right.trans ((source_Z_Q_U h c).1.trans (map_subtype_le _))))
  obtain ⟨g,hg,hga⟩ := source_cubic_center_pair_transitive h hc hb hbc hac hcard c hbc
  apply le_antisymm
  · intro x hx
    refine ⟨?_,hx.2⟩
    have hm := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx.2
    rw [←Z_translate,←hga,inv_smul_smul] at hm
    have hh := (mem_centralizer_iff.mp (hcentral ((Z (family P) a ⊔ Z (family P) c).inv_mem hg))) x hx
    change g⁻¹ * x * (g⁻¹)⁻¹ ∈ Z (family P) a at hm
    change x ∈ Z (family P) a
    simpa only [←hh,mul_inv_cancel_right] using hm
  · exact inf_le_inf_right _ ((source_Z_Q_U h a).1.trans (map_subtype_le _))

private theorem stabilizer_normalizes_core (a : Vertex (family P)) :
    stabilizer (family P) a ≤ normalizer (Q (family P) a : Set G) :=
  (stabilizer (family P) a).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer (family P) a)))

private theorem stabilizer_normalizes_center (h : LocallyRankOneTriple P B)
    (a : Vertex (family P)) :
    stabilizer (family P) a ≤ normalizer (Z (family P) a : Set G) := by
  let := finite_endpoints h
  exact (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ a)).mp (Z_normal _ a)

private theorem core_le_adjacent_stabilizer (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    Q (family P) a ≤ stabilizer (family P) b :=
  (source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)

/-- The source layer Z₀ centralizes Qα by faithful-graph normalizer propagation. -/
theorem source_cubic_a5_layer_centralizes_core (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) ≤
      centralizer (Q (family P) a : Set G) := by
  let := finite_endpoints h
  let I := neighborCoreIntersection (family P) b
  let J := I ⊓ Q (family P) (g • b)
  let N := J ⊔ Z (family P) a
  let C := Z (family P) c ⊓ Q (family P) b
  let D := Z (family P) (g • c) ⊓ Q (family P) (g • b)
  have hab := source_critical_one_adjacent hc hb
  have hga' : g • a = a := hga
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [hga'] at hh
  have hIqa : I ≤ Q (family P) a := neighborCoreIntersection_le _ hab
  have hJqa : J ≤ Q (family P) a := inf_le_left.trans hIqa
  have hCQ : C ≤ Q (family P) b := inf_le_right
  have hCga : C ≤ stabilizer (family P) a := hCQ.trans (core_le_adjacent_stabilizer h hab.symm)
  have hDga : D ≤ stabilizer (family P) a := inf_le_right.trans
    (core_le_adjacent_stabilizer h hab'.symm)
  have hQaJ : Q (family P) a ≤ normalizer (J : Set G) :=
    (le_inf ((core_le_adjacent_stabilizer h hab).trans (neighborCoreIntersection_normalized _ b))
      (source_adjacent_core_normalizes_core h hab')).trans inf_normalizer_le_normalizer_inf
  have hQaN : Q (family P) a ≤ normalizer (N : Set G) :=
    (le_inf hQaJ ((Q_le_stabilizer _ a).trans (stabilizer_normalizes_center h a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hCJ : C ≤ centralizer (J : Set G) := inf_le_left.trans
    ((le_centralizer_iff.mp (source_core_centralizes_center h c)).trans
      (centralizer_le (inf_le_left.trans (neighborCoreIntersection_le _ hbc.symm))))
  have hCN : C ≤ normalizer (N : Set G) :=
    (le_inf (hCJ.trans (Subgroup.centralizer_le_normalizer _))
      (hCga.trans (stabilizer_normalizes_center h a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJD : ⁅J,D⁆ ≤ Z (family P) a := by
    have h₁ : ⁅J,D⁆ ≤ Q (family P) a :=
      (commutator_mono hJqa le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hDga.trans (stabilizer_normalizes_core a)))
    have h₂ : ⁅J,D⁆ ≤ Z (family P) (g • c) :=
      (commutator_mono inf_le_right inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp
          (source_adjacent_core_normalizes_center h
            ((Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc).symm))
    have hid := congrArg (map (MulAut.conj g).toMonoidHom)
      (source_cubic_core_inf_center h hc hb hbc hac hcard)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←Q_translate,←Z_translate,←Z_translate,hga'] at hid
    exact (le_inf h₁ h₂).trans (hid.le.trans inf_le_left)
  have hDN : D ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply commutator_sup_le_of_relative_normal N J (Z (family P) a) D N
      N.le_normalizer le_sup_left le_sup_right
    · exact hJD.trans le_sup_right
    · exact (le_normalizer_iff_commutator_le_left.mp
        (hDga.trans (stabilizer_normalizes_center h a))).trans le_sup_right
  have hnorm : stabilizer (family P) a ≤ normalizer (N : Set G) := by
    rw [←source_cubic_a5_opposite_seed_generation h hB hS hc hb hbc hac hcard e g hga hgb]
    exact sup_le (sup_le hCN hDN) hQaN
  let E := ⁅N,Q (family P) a⁆
  have hEJ : E ≤ J := by
    apply commutator_sup_le_of_relative_normal (Q (family P) a)
      J (Z (family P) a) (Q (family P) a) J hQaJ hJqa
      ((source_Z_Q_U h a).1.trans (map_subtype_le _))
    · exact le_normalizer_iff_commutator_le_left.mp hQaJ
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (source_core_centralizes_center h a))).le.trans bot_le
  have hEn : stabilizer (family P) a ≤ normalizer (E : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change E.map (MulAut.conj t).toMonoidHom = E
    have hnmap : N.map (MulAut.conj t).toMonoidHom = N :=
      mem_normalizer_iff_map_conj_eq.mp (hnorm ht)
    have hqmap : (Q (family P) a).map (MulAut.conj t).toMonoidHom = Q (family P) a :=
      mem_normalizer_iff_map_conj_eq.mp (stabilizer_normalizes_core a ht)
    rw [map_commutator,hnmap,hqmap]
  have hE : E = ⊥ := by
    apply CommutingNontrivial.source_normalized_edge_eq_bot h hab E
      (hEJ.trans (le_inf (hJqa.trans (Q_le_stabilizer _ a))
        (hJqa.trans (core_le_adjacent_stabilizer h hab))))
    · intro v hv
      obtain ⟨t,ht,he⟩ := locally_transitive (family P) hab hv
      exact ⟨t,hEn ht,he⟩
    · intro v hv
      obtain ⟨t,ht,he⟩ := source_neighbor_core_centralizer_transitive h hB hc hb hv
      exact ⟨t,Subgroup.centralizer_le_normalizer _
        (centralizer_le (hEJ.trans inf_le_left) ht.2),he⟩
  exact commutator_eq_bot_iff_le_centralizer.mp
    (bot_unique ((commutator_mono le_sup_left le_rfl).trans hE.le))


/-- The elementary source layer Z₀ lies in Zβ via the actual edge Sylow. -/
theorem source_cubic_a5_layer_le_center (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) ≤
      Z (family P) b := by
  let J := neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b)
  have hab := source_critical_one_adjacent hc hb
  have hga' : g • a = a := hga
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [hga'] at hh
  have hbc' : (graph (family P)).Adj (g • b) (g • c) :=
    (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc
  have hac' : a ≠ g • c := by
    intro he
    apply hac
    have hh := congrArg (fun v => g⁻¹ • v) he
    rwa [←hga',inv_smul_smul,inv_smul_smul] at hh
  let : IsElementaryAbelian 2 J := (source_cubic_a5_intersection_layer h hB hS hc hb
    hcard e hab' (Ne.symm hgb) hbc' hac').1
  have he := source_cubic_a5_edge_core_eq_seed_sup_core h hB hS hc hb hbc hac hcard e
  apply elementary_central_edge_le_center h hB hS hab J
  · rw [he]
    exact (inf_le_left.trans (neighborCoreIntersection_le _ hab)).trans le_sup_right
  · rw [he]
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact inf_le_left.trans ((le_centralizer_iff.mp (source_core_centralizes_center h c)).trans
        (centralizer_le (inf_le_left.trans (neighborCoreIntersection_le _ hbc.symm))))
    · exact le_centralizer_iff.mp
        (source_cubic_a5_layer_centralizes_core h hB hS hc hb hbc hac hcard e g hga hgb)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

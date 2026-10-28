module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Distances
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicNonedges
public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleHomotopy

/-!
# Common neighbors of source A₅ pairs

For a source nonedge generating A₅, the intrinsic cubic-pair calculation
constructs a square of four distinct common neighbors in that very subgroup.
The ambient four-neighbor count exhausts the common neighbors, proving both
containment in the generated A₅ and connectivity. Conjugation transports
these statements to every source pair. The remaining connectivity premise
is reduced by the source suborbit action to a single SL₂(3) pair.

Source: Aschbacher, *Sporadic Groups* (1994), 47.7(3), p.265. This discharges
the A₅ branch of the square contraction used in 47.9; it does not assert
47.8, pentagon contraction, or recognition from J₂-type alone.
-/

public section
open Subgroup MulAction
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.CommonNeighbors
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
private theorem base_a5_square (D : Seed G) (Y : D.Vertex)
    (hY : a5Join D D.base Y) :
    ∃ R : Fin 4 → D.Vertex, Function.Injective R ∧
      (∀ i, (R i).val ≤ D.X ⊔ Y.val) ∧
      (∀ i, D.graph.Adj D.base (R i) ∧ D.graph.Adj Y (R i)) ∧
      (∀ i, D.graph.Adj (R i) (R (i + 1))) := by
  let K := D.X ⊔ Y.val
  let eK : K ≃* alternatingGroup (Fin 5) := hY.some
  have hX : D.X ≤ K := le_sup_left
  have hYK : Y.val ≤ K := le_sup_right
  have hc (A : Subgroup G) (hA : Nat.card A = 3) (hAK : A ≤ K) :
      Nat.card (A.subgroupOf K) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv, hA]
  have htop : D.X.subgroupOf K ⊔ Y.val.subgroupOf K = ⊤ := by
    rw [← subgroupOf_sup hX hYK]
    exact subgroupOf_self K
  obtain ⟨S, hinj, hs, hx, hy, hedges⟩ :=
    alternatingGroup.FiveLocalGeometry.CubicNonedges.exists_common_square eK
      (D.X.subgroupOf K) (Y.val.subgroupOf K)
      (hc _ D.card_X hX) (hc _ (D.vertex_card Y) hYK) htop
  let R (i : Fin 4) : D.Vertex := ⟨(S i).map K.subtype,
    AlternatingFiveGeometry.mem_vertex_of_card_three D K eK hX _
      (by rw [card_map_of_injective K.subtype_injective, hs]) (map_subtype_le _)⟩
  have hr (i : Fin 4) : (R i).val.subgroupOf K = S i :=
    comap_map_eq_self_of_injective K.subtype_injective (S i)
  have hR (i : Fin 4) : (R i).val ≤ K := map_subtype_le _
  have lift (A B : D.Vertex) (hA : A.val ≤ K) (hB : B.val ≤ K)
      (h : Nonempty (↥(A.val.subgroupOf K ⊔ B.val.subgroupOf K) ≃*
        alternatingGroup (Fin 4))) : D.graph.Adj A B := by
    exact (D.graph_adj_iff A B).mpr
      ⟨(AlternatingFiveGeometry.joinSubgroupOfEquiv K A.val B.val hA hB).symm.trans h.some⟩
  refine ⟨R, ?_, hR, ?_, ?_⟩
  · intro i j hij
    apply hinj
    have h := congrArg (fun T : D.Vertex => T.val.subgroupOf K) hij
    simpa only [hr] using h
  · intro i
    constructor
    · apply lift D.base (R i) hX (hR i)
      rw [hr]
      exact hx i
    · apply lift Y (R i) hYK (hR i)
      rw [hr]
      exact hy i
  · intro i
    apply lift (R i) (R (i + 1)) (hR i) (hR (i + 1))
    rw [hr, hr]
    exact hedges i

/-- In the A₅ nonedge case every common neighbor lies in the generated A₅,
and its common-neighbor graph is connected (source 47.7(3)). -/
theorem base_a5_connected (D : Seed G) (Y : D.Vertex)
    (hY : a5Join D D.base Y) :
    (∀ U, D.graph.Adj D.base U → D.graph.Adj Y U → U.val ≤ D.X ⊔ Y.val) ∧
      (D.graph.commonNeighborGraph D.base Y).Preconnected := by
  have hc := card_join_of_a5Join D hY
  have hne : Y ≠ D.base := by
    intro he
    rw [he, sup_idem, D.vertex_card] at hc
    omega
  have hn : ¬ D.graph.Adj D.base Y := by
    intro ha
    have hc' := card_join_of_adj D ha
    omega
  have hcard : Nat.card {U : D.Vertex // D.graph.Adj D.base U ∧ D.graph.Adj Y U} = 4 := by
    change Nat.card ({U | D.graph.Adj D.base U ∧ D.graph.Adj Y U} : Set D.Vertex) = 4
    rw [Nat.card_coe_set_eq]
    exact EdgeConfigurations.Distances.common_neighbors_card D Y hne hn
  obtain ⟨R, hinj, hle, hadj, hedge⟩ := base_a5_square D Y hY
  let f (i : Fin 4) : {U : D.Vertex // D.graph.Adj D.base U ∧ D.graph.Adj Y U} :=
    ⟨R i, hadj i⟩
  have hf : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨fun i j h =>
      hinj (congrArg Subtype.val h), by rw [Nat.card_fin, hcard]⟩).2
  have edge (i : Fin 4) : (D.graph.commonNeighborGraph D.base Y).Adj (f i) (f (i + 1)) :=
    hedge i
  have reach (i : Fin 4) : (D.graph.commonNeighborGraph D.base Y).Reachable (f 0) (f i) := by
    fin_cases i
    · exact SimpleGraph.Reachable.refl _
    · exact (edge 0).reachable
    · exact (edge 0).reachable.trans (edge 1).reachable
    · exact (edge 3).reachable.symm
  constructor
  · intro U hU hUY
    obtain ⟨i, hi⟩ := hf ⟨U, hU, hUY⟩
    have he : R i = U := congrArg Subtype.val hi
    exact he ▸ hle i
  · intro U V
    obtain ⟨i, rfl⟩ := hf U
    obtain ⟨j, rfl⟩ := hf V
    exact (reach i).symm.trans (reach j)

/-- Conjugation transports the literal common-neighbor graph. -/
private def smulCommonHom (D : Seed G) (g : G) (A B : D.Vertex) :
    D.graph.commonNeighborGraph A B →g D.graph.commonNeighborGraph (g • A) (g • B) where
  toFun U := ⟨g • U.val, D.preserves g U.property.1, D.preserves g U.property.2⟩
  map_rel' h := D.preserves g h

omit [IsSimpleGroup G] in
private theorem smulCommonHom_surjective (D : Seed G) (g : G) (A B : D.Vertex) :
    Function.Surjective (smulCommonHom D g A B) := by
  intro U
  refine ⟨⟨g⁻¹ • U.val, ?_, ?_⟩, Subtype.ext (smul_inv_smul _ _)⟩
  · simpa only [inv_smul_smul] using D.preserves g⁻¹ U.property.1
  · simpa only [inv_smul_smul] using D.preserves g⁻¹ U.property.2

/-- The A₅ branch is proved for every pair in the arbitrary source graph,
including containment in the literal generated subgroup. -/
theorem a5_connected (D : Seed G) (A B : D.Vertex) (hAB : a5Join D A B) :
    (∀ U, D.graph.Adj A U → D.graph.Adj B U → U.val ≤ A.val ⊔ B.val) ∧
      (D.graph.commonNeighborGraph A B).Preconnected := by
  obtain ⟨g, rfl⟩ := D.transitive A
  have hj : a5Join D D.base (g⁻¹ • B) := by
    simpa only [inv_smul_smul] using (a5Join_smul_iff D g⁻¹ (g • D.base) B).mpr hAB
  obtain ⟨hle, hconn⟩ := base_a5_connected D (g⁻¹ • B) hj
  constructor
  · intro U hU hBU
    have hXU : D.graph.Adj D.base (g⁻¹ • U) := by
      simpa only [inv_smul_smul] using D.preserves g⁻¹ hU
    have h := hle (g⁻¹ • U) hXU (D.preserves g⁻¹ hBU)
    have hm := Subgroup.map_mono h (f := (MulAut.conj g).toMonoidHom)
    change (g⁻¹ • U).val.map (MulAut.conj g).toMonoidHom ≤
      (D.base.val ⊔ (g⁻¹ • B).val).map (MulAut.conj g).toMonoidHom at hm
    rw [Subgroup.map_sup, ← D.smul_val, ← D.smul_val, ← D.smul_val,
      smul_inv_smul, smul_inv_smul] at hm
    exact hm
  · have h := hconn.map (smulCommonHom D g D.base (g⁻¹ • B))
      (smulCommonHom_surjective D g D.base (g⁻¹ • B))
    rw [smul_inv_smul] at h
    exact h

/-- The A₅ branch and source suborbit transitivity leave just one SL₂(3)
pair for the square-contraction premise. -/
theorem connected_of_one_sl2 (D : Seed G) (Y : D.Vertex)
    (hY : sl2Join D D.base Y)
    (hconn : (D.graph.commonNeighborGraph D.base Y).Preconnected)
    (A B : D.Vertex) (hne : A ≠ B) (hn : ¬ D.graph.Adj A B) :
    (D.graph.commonNeighborGraph A B).Preconnected := by
  have base (Z : D.Vertex) (hZ : D.base ≠ Z) (hnZ : ¬ D.graph.Adj D.base Z) :
      (D.graph.commonNeighborGraph D.base Z).Preconnected := by
    rcases (InvolutionGeometry.Applications.fourSuborbits D).joins D.base Z with he | ha | hs | hf
    · exact (hZ he).elim
    · exact (hnZ ha).elim
    · obtain ⟨g, hg⟩ := (InvolutionGeometry.Applications.fourSuborbits D).transitive Y Z
        ((orbitLabel_of_sl2Join D hY).trans (orbitLabel_of_sl2Join D hs).symm)
      have h := hconn.map (smulCommonHom D (g : G) D.base Y)
        (smulCommonHom_surjective D (g : G) D.base Y)
      rw [normalizer_fixes_base D g, hg] at h
      exact h
    · exact (base_a5_connected D Z hf).2
  obtain ⟨g, rfl⟩ := D.transitive A
  have hne' : D.base ≠ g⁻¹ • B := by
    intro he
    apply hne
    rw [he, smul_inv_smul]
  have hn' : ¬ D.graph.Adj D.base (g⁻¹ • B) := by
    intro ha
    apply hn
    have h := D.preserves g ha
    rwa [smul_inv_smul] at h
  have h := (base (g⁻¹ • B) hne' hn').map (smulCommonHom D g D.base (g⁻¹ • B))
    (smulCommonHom_surjective D g D.base (g⁻¹ • B))
  rw [smul_inv_smul] at h
  exact h

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.CommonNeighbors

module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceComparison.Local
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdgeAdjustment

/-!
# The source-to-ATLAS similarity for J₂ recognition

The prescribed S₃ overlap map extends across the local A₅. An automorphism
fixing this S₃ pointwise chooses the correct orbit of adjacent cubics;
conjugation by a member of X then aligns the second endpoint. Applying the
same conjugation to the vertex-group map preserves agreement, and X
centralizes the full pointwise edge fixer. Transport of the two literal
endpoint subgroups proves the setwise-edge condition.

Thus both local isomorphisms and every compatibility field of `Similarity`
are constructed from the original source seed. The two triangle orbits
remain distinct. Global recognition still requires the cycle-base argument.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceComparison
open SourceLocal SourceLocal.PrimeNormalizers.ThreeLocal
open Theory.GroupTheory.GraphUniquenessSystem
open Sporadic.LeechRelated.J2
open alternatingGroup.FiveLocalGeometry.CubicEdges
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

private theorem target_X_normalizes_E {x : Carrier} (hx : x ∈ RecognitionGeometry.X) :
    x ∈ normalizer (RecognitionGeometry.E : Set Carrier) := by
  let e : RecognitionGeometry.E.subgroupOf RecognitionGeometry.M ≃* alternatingGroup (Fin 5) :=
    (subgroupOfEquivOfLe (show RecognitionGeometry.E ≤ RecognitionGeometry.M from inf_le_left)).trans
      RecognitionGeometry.LocalA5.edgeEquiv
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (RecognitionGeometry.E.subgroupOf RecognitionGeometry.M) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hle : RecognitionGeometry.E ≤ RecognitionGeometry.VertexExtension.C := by
    have h := le_of_isPerfect_of_index_eq_two
      (RecognitionGeometry.E.subgroupOf RecognitionGeometry.M)
      RecognitionGeometry.VertexExtension.CM RecognitionGeometry.VertexExtension.centralizer_index
    intro b hb
    exact h (show (⟨b, hb.1⟩ : RecognitionGeometry.M) ∈
      RecognitionGeometry.E.subgroupOf RecognitionGeometry.M from hb)
  apply (Subgroup.centralizer_le_normalizer _)
  apply mem_centralizer_iff.mpr
  intro b hb
  have hz : (⟨x, RecognitionGeometry.VertexExtension.X_le_C hx⟩ :
      RecognitionGeometry.VertexExtension.C) ∈ center RecognitionGeometry.VertexExtension.C := by
    rw [RecognitionGeometry.VertexExtension.center_C_eq_XC ConcreteSystem.card_M]
    exact hx
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨b, hle hb⟩)

/-- Align both local endpoint subgroups, retaining the agreement and full edge fixer. -/
theorem aligned_local_maps (D : Seed G) (F : EdgeFrame D) :
    ∃ (eM : M D ≃* RecognitionGeometry.M) (eK : F.K ≃* RecognitionGeometry.K),
      (D.X.subgroupOf F.K).map eK.toMonoidHom =
        RecognitionGeometry.X.subgroupOf RecognitionGeometry.K ∧
      (F.y.val.subgroupOf F.K).map eK.toMonoidHom =
        RecognitionGeometry.Y.subgroupOf RecognitionGeometry.K ∧
      (∀ (g : G) (hgK : g ∈ F.K) (hgM : g ∈ M D),
        (eM ⟨g, hgM⟩ : Carrier) = (eK ⟨g, hgK⟩ : Carrier)) ∧
      (∀ m : M D, (m : G) ∈ edgeFixer G D.base F.y ↔
        (eM m : Carrier) ∈ RecognitionGeometry.E) := by
  obtain ⟨e, _, hE, hB⟩ := marked_edge_comparison D F
  obtain ⟨d, hdX, hagree, hv⟩ := local_comparison D F e
    (vertex_overlap_of_marked D F e hB)
  have hsource := F.endpoints_le (InvolutionGeometry.Applications.edgeFixer_equiv D F.adjacent)
  have hsX : D.X ≤ F.K := le_sup_left.trans hsource
  have hsY : F.y.val ≤ F.K := le_sup_right.trans hsource
  have htX : RecognitionGeometry.X ≤ RecognitionGeometry.K :=
    le_sup_left.trans RecognitionGeometry.X_sup_Y_le_K
  have htY : RecognitionGeometry.Y ≤ RecognitionGeometry.K :=
    le_sup_right.trans RecognitionGeometry.X_sup_Y_le_K
  let P := RecognitionGeometry.X.subgroupOf RecognitionGeometry.K
  let Q := (F.y.val.subgroupOf F.K).map d.toMonoidHom
  let R := RecognitionGeometry.Y.subgroupOf RecognitionGeometry.K
  have hjoin : (D.X.subgroupOf F.K ⊔ F.y.val.subgroupOf F.K).map d.toMonoidHom = P ⊔ Q := by
    rw [Subgroup.map_sup, hdX]
  let sourceJ := (AlternatingFiveGeometry.joinSubgroupOfEquiv F.K D.X F.y.val hsX hsY).trans
    ((D.graph_adj_iff D.base F.y).mp F.adjacent).some
  let ePQ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4) :=
    (MulEquiv.subgroupCongr hjoin.symm).trans
      ((MulEquiv.subgroupMap d _).symm.trans sourceJ)
  let ePR := (AlternatingFiveGeometry.joinSubgroupOfEquiv RecognitionGeometry.K
    RecognitionGeometry.X RecognitionGeometry.Y htX htY).trans RecognitionGeometry.edgeEquiv
  obtain ⟨z, a, ha, hY⟩ := adjust_neighbor RecognitionGeometry.LocalA5.localEquiv P Q R
    (by rw [Nat.card_congr (subgroupOfEquivOfLe htX).toEquiv, RecognitionGeometry.card_X])
    (by rw [card_map_of_injective d.injective,
      Nat.card_congr (subgroupOfEquivOfLe hsY).toEquiv, D.vertex_card])
    (by rw [Nat.card_congr (subgroupOfEquivOfLe htY).toEquiv, RecognitionGeometry.card_Y]) ePQ ePR
  let zm : RecognitionGeometry.M := ⟨z.val, RecognitionGeometry.X.le_normalizer z.property⟩
  let eM := e.trans (MulAut.conj zm)
  let eK := d.trans (a.trans (MulAut.conj (z : RecognitionGeometry.K)))
  have haP : P.map a.toMonoidHom = P := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change a x ∈ P
      rwa [ha x (P.le_normalizer hx)]
    · intro x hx
      exact ⟨x, hx, ha x (P.le_normalizer hx)⟩
  have heX : (D.X.subgroupOf F.K).map eK.toMonoidHom = P := by
    change (D.X.subgroupOf F.K).map
      ((MulAut.conj (z : RecognitionGeometry.K)).toMonoidHom.comp
        (a.toMonoidHom.comp d.toMonoidHom)) = P
    rw [← map_map, ← map_map, hdX, haP]
    exact mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer z.property)
  refine ⟨eM, eK, heX, ?_, ?_, ?_⟩
  · change (F.y.val.subgroupOf F.K).map
      ((a.trans (MulAut.conj (z : RecognitionGeometry.K))).toMonoidHom.comp d.toMonoidHom) = R
    rw [← map_map]
    exact hY
  · intro g hgK hgM
    have hdM : (d ⟨g, hgK⟩ : Carrier) ∈ RecognitionGeometry.M := (hv _).mp hgM
    have hdN : d ⟨g, hgK⟩ ∈ normalizer (P : Set RecognitionGeometry.K) := by
      rw [← subgroupOf_normalizer_eq htX]
      exact hdM
    have hh := ha (d ⟨g, hgK⟩) hdN
    change (zm : Carrier) * (e ⟨g, hgM⟩ : Carrier) * (zm : Carrier)⁻¹ =
      (z.val : Carrier) * (a (d ⟨g, hgK⟩) : Carrier) * (z.val : Carrier)⁻¹
    rw [hh, hagree g hgK hgM]
  · intro m
    apply (hE m).trans
    exact (mem_normalizer_iff.mp (target_X_normalizes_E z.property)) (e m)

private theorem conj_restriction {A : Type*} [Group A] (K U V : Subgroup A)
    (hU : U ≤ K) (hV : V ≤ K) (g : K) :
    (U.subgroupOf K).map (MulAut.conj g).toMonoidHom = V.subgroupOf K ↔
      U.map (MulAut.conj (g : A)).toMonoidHom = V := by
  change MulAut.conj g • U.subgroupOf K = V.subgroupOf K ↔ _
  rw [conj_smul_subgroupOf hU g]
  constructor
  · intro h
    have hm := congrArg (fun P : Subgroup K => P.map K.subtype) h
    rw [map_subgroupOf_eq_of_le (conj_smul_le_of_le hU g), map_subgroupOf_eq_of_le hV] at hm
    exact hm
  · intro h
    change (U.map (MulAut.conj (g : A)).toMonoidHom).subgroupOf K = _
    rw [h]

private theorem source_local_edge (D : Seed G) (F : EdgeFrame D) (g : F.K) :
    (g : G) ∈ edgeStabilizer G D.base F.y ↔
      g ∈ pairStabilizer (D.X.subgroupOf F.K) (F.y.val.subgroupOf F.K) := by
  have h := F.endpoints_le (InvolutionGeometry.Applications.edgeFixer_equiv D F.adjacent)
  have hx : D.X ≤ F.K := le_sup_left.trans h
  have hy : F.y.val ≤ F.K := le_sup_right.trans h
  change (((g : G) • D.base = D.base ∧ (g : G) • F.y = F.y) ∨
    ((g : G) • D.base = F.y ∧ (g : G) • F.y = D.base)) ↔ _
  simp only [Subtype.ext_iff, D.smul_val, Seed.base]
  rw [← conj_restriction F.K D.X D.X hx hx,
    ← conj_restriction F.K F.y.val F.y.val hy hy,
    ← conj_restriction F.K D.X F.y.val hx hy,
    ← conj_restriction F.K F.y.val D.X hy hx]
  rfl

private theorem target_local_edge (g : RecognitionGeometry.K) :
    (g : Carrier) ∈ edgeStabilizer Carrier RecognitionGeometry.base RecognitionGeometry.neighbor ↔
      g ∈ pairStabilizer (RecognitionGeometry.X.subgroupOf RecognitionGeometry.K)
        (RecognitionGeometry.Y.subgroupOf RecognitionGeometry.K) := by
  have hx : RecognitionGeometry.X ≤ RecognitionGeometry.K :=
    le_sup_left.trans RecognitionGeometry.X_sup_Y_le_K
  have hy : RecognitionGeometry.Y ≤ RecognitionGeometry.K :=
    le_sup_right.trans RecognitionGeometry.X_sup_Y_le_K
  change (((g : Carrier) • RecognitionGeometry.base = RecognitionGeometry.base ∧
    (g : Carrier) • RecognitionGeometry.neighbor = RecognitionGeometry.neighbor) ∨
    ((g : Carrier) • RecognitionGeometry.base = RecognitionGeometry.neighbor ∧
    (g : Carrier) • RecognitionGeometry.neighbor = RecognitionGeometry.base)) ↔ _
  simp only [Subtype.ext_iff, RecognitionGeometry.smul_val, RecognitionGeometry.base, RecognitionGeometry.neighbor]
  rw [← conj_restriction RecognitionGeometry.K RecognitionGeometry.X RecognitionGeometry.X hx hx,
    ← conj_restriction RecognitionGeometry.K RecognitionGeometry.Y RecognitionGeometry.Y hy hy,
    ← conj_restriction RecognitionGeometry.K RecognitionGeometry.X RecognitionGeometry.Y hx hy,
    ← conj_restriction RecognitionGeometry.K RecognitionGeometry.Y RecognitionGeometry.X hy hx]
  rfl

/-- The source and concrete uniqueness systems are similar, with every local
comparison premise discharged from the original seed. -/
theorem source_similarity (D : Seed G) :
    Nonempty (Similarity (sourceSystem D) ConcreteSystem.system) := by
  obtain ⟨e, d, hdX, hdY, hagree, hedge⟩ := aligned_local_maps D (sourceFrame D)
  have hM : (sourceSystem D).vertexGroup = M D := D.stabilizer_eq_normalizer D.base
  let eM := (MulEquiv.subgroupCongr hM).trans
    (e.trans (MulEquiv.subgroupCongr ConcreteSystem.system_vertexGroup.symm))
  let eK : (sourceSystem D).H ≃* ConcreteSystem.system.H :=
    d.trans (MulEquiv.subgroupCongr ConcreteSystem.system_local.symm)
  refine ⟨⟨eM, eK, ?_, ?_, ?_, ?_⟩⟩
  · intro g hgK hgM
    exact hagree g hgK (hM ▸ hgM)
  · intro g
    change ↥(sourceFrame D).K at g
    rw [hM, ConcreteSystem.system_vertexGroup]
    have hsX : D.X ≤ (sourceFrame D).K := le_sup_left.trans
      ((sourceFrame D).endpoints_le
        (InvolutionGeometry.Applications.edgeFixer_equiv D (sourceFrame D).adjacent))
    have htX : RecognitionGeometry.X ≤ RecognitionGeometry.K :=
      le_sup_left.trans RecognitionGeometry.X_sup_Y_le_K
    change g ∈ (normalizer (D.X : Set G)).subgroupOf (sourceFrame D).K ↔
      d g ∈ (normalizer (RecognitionGeometry.X : Set Carrier)).subgroupOf RecognitionGeometry.K
    rw [subgroupOf_normalizer_eq hsX, subgroupOf_normalizer_eq htX]
    have hn := map_equiv_normalizer_eq (D.X.subgroupOf (sourceFrame D).K) d
    rw [hdX] at hn
    rw [← hn, mem_map_equiv, d.symm_apply_apply]
  · intro m
    rw [ConcreteSystem.system_edgeGroup]
    exact hedge (MulEquiv.subgroupCongr hM m)
  · intro g
    change ↥(sourceFrame D).K at g
    change (g : G) ∈ edgeStabilizer G D.base (sourceFrame D).y ↔
      (d g : Carrier) ∈ edgeStabilizer Carrier ConcreteSystem.system.x ConcreteSystem.system.y
    rw [ConcreteSystem.system_base, ConcreteSystem.system_neighbor,
      source_local_edge, target_local_edge]
    have h := mem_pairStabilizer_map_iff d (D.X.subgroupOf (sourceFrame D).K)
      ((sourceFrame D).y.val.subgroupOf (sourceFrame D).K) g
    rwa [hdX, hdY] at h

end CFSG.Quasithin.Janko23.J2Recognition.SourceComparison

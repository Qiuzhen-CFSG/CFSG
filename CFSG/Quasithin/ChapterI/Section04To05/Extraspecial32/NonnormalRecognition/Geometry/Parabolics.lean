module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Parabolics.Quotient
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Parabolics.MarkedTransport
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.ElementaryNormalizer

/-!
# The three literal parabolic pairs of the source configuration

Let M = N_G(E), K = N_G(A), R = N_G(F). The endpoint intersection is H,
and M ∩ K ∩ R is the specified Sylow two-subgroup, of order 64. Once the
split-extension calculation gives |M ∩ K| = |R ∩ K| = 192, prime indices
make all six local intersections maximal. The genuine quotient maps to
PSL₃(2) and S₃ × S₃ give exhaustiveness over the chamber. The two distinct
maximal subgroups in K generate K, proving K ≤ M ⊔ R before restriction
to the geometry group. Thus none of the ambient normalizers is truncated.

The faithful conjugation actions and the supplied complements identify both
endpoint normalizers with the genuine natural split block. Its elementary
sixteen-group calculation identifies N_M(A) and N_R(A) with the stabilizers
of the actual order-four intersections A ∩ E and A ∩ F, and supplies both
overlap orders. `configuration_parabolics` thus proves all the local
parabolic assertions from the configuration, with no additional model or
cardinality premise. `geometry_of_split_configuration` applies this to the
fusion count and D-system construction. Constructing the source configuration
remains the earlier Lemma 3.1 step; no recognition of L is assumed here.

Source: M. Aschbacher, “A 2-local characterization of M12”, Lemma 3.2,
printed p.37, using the split extensions of Lemma 3.1.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition
namespace Parabolics

variable {G : Type*} [Group G]

theorem card_subgroupOf (M N : Subgroup G) :
    Nat.card (N.subgroupOf M) = Nat.card (M ⊓ N : Subgroup G) :=
  Nat.card_congr {
    toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
    invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem pair_inf (M N R : Subgroup G) :
    N.subgroupOf M ⊓ R.subgroupOf M = (M ⊓ N ⊓ R).subgroupOf M := by
  ext x
  exact ⟨fun hx => ⟨⟨x.property, hx.1⟩, hx.2⟩, fun hx => ⟨hx.1.2, hx.2⟩⟩

theorem pair_parabolics_PSL [Finite G] (M N R E : Subgroup G)
    (hn : (E.subgroupOf M).Normal) (hp : IsPGroup 2 (E.subgroupOf M))
    (eqt : Nonempty ((M ⧸ E.subgroupOf M) ≃* Matrix.PSL3Two.PSL))
    (hm : Nat.card M = 1344)
    (hN : Nat.card (M ⊓ N : Subgroup G) = 192)
    (hR : Nat.card (M ⊓ R : Subgroup G) = 192)
    (hB : Nat.card (M ⊓ N ⊓ R : Subgroup G) = 64) :
    Quasithin.I5.RankTwoParabolics M ((M ⊓ N ⊓ R).subgroupOf M)
      (N.subgroupOf M) (R.subgroupOf M) := by
  have hbc : Nat.card ((M ⊓ N ⊓ R).subgroupOf M) = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv]
    exact hB
  let S : Sylow 2 M := Sylow.ofCard ((M ⊓ N ⊓ R).subgroupOf M) (by
    rw [hbc, hm]; decide +kernel)
  apply rankTwo_of_prime_indices _ _ _
    (hasTwoMaximalOvergroups_quotient (E.subgroupOf M) hp eqt.some
      hasTwoMaximalOvergroups_PSL S)
  · have hc := (N.subgroupOf M).card_mul_index
    rw [card_subgroupOf, hN, hm] at hc
    have he : (N.subgroupOf M).index = 7 := by omega
    rw [he]; decide
  · have hc := (R.subgroupOf M).card_mul_index
    rw [card_subgroupOf, hR, hm] at hc
    have he : (R.subgroupOf M).index = 7 := by omega
    rw [he]; decide
  · exact pair_inf M N R
  · change Nat.card ((M ⊓ N ⊓ R).subgroupOf M) < Nat.card (N.subgroupOf M)
    rw [hbc, card_subgroupOf, hN]; decide

theorem pair_parabolics_product [Finite G] (M N R A : Subgroup G)
    (hn : (A.subgroupOf M).Normal) (hp : IsPGroup 2 (A.subgroupOf M))
    (eqt : Nonempty ((M ⧸ A.subgroupOf M) ≃* SymmetricThreeProduct.G))
    (hm : Nat.card M = 576)
    (hN : Nat.card (M ⊓ N : Subgroup G) = 192)
    (hR : Nat.card (M ⊓ R : Subgroup G) = 192)
    (hB : Nat.card (M ⊓ N ⊓ R : Subgroup G) = 64) :
    Quasithin.I5.RankTwoParabolics M ((M ⊓ N ⊓ R).subgroupOf M)
      (N.subgroupOf M) (R.subgroupOf M) := by
  have hbc : Nat.card ((M ⊓ N ⊓ R).subgroupOf M) = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv]
    exact hB
  let S : Sylow 2 M := Sylow.ofCard ((M ⊓ N ⊓ R).subgroupOf M) (by
    rw [hbc, hm]; decide +kernel)
  apply rankTwo_of_prime_indices _ _ _
    (hasTwoMaximalOvergroups_quotient (A.subgroupOf M) hp eqt.some
      hasTwoMaximalOvergroups_product S)
  · have hc := (N.subgroupOf M).card_mul_index
    rw [card_subgroupOf, hN, hm] at hc
    have he : (N.subgroupOf M).index = 3 := by omega
    rw [he]; decide
  · have hc := (R.subgroupOf M).card_mul_index
    rw [card_subgroupOf, hR, hm] at hc
    have he : (R.subgroupOf M).index = 3 := by omega
    rw [he]; decide
  · exact pair_inf M N R
  · change Nat.card ((M ⊓ N ⊓ R).subgroupOf M) < Nat.card (N.subgroupOf M)
    rw [hbc, card_subgroupOf, hN]; decide

theorem middle_le_of_generate (M K R L : Subgroup G) (hm : M ≤ L) (hr : R ≤ L)
    (hg : M.subgroupOf K ⊔ R.subgroupOf K = ⊤) : K ≤ L := by
  have hle : M.subgroupOf K ⊔ R.subgroupOf K ≤ L.subgroupOf K :=
    sup_le (comap_mono hm) (comap_mono hr)
  rw [hg] at hle
  intro x hx
  exact hle (show (⟨x, hx⟩ : K) ∈ (⊤ : Subgroup K) from mem_top _)

end Parabolics

variable {G : Type*} [Group G] [Finite G] {z g : G}

theorem configuration_triple_card (h : Hypotheses z) (d : IntersectionData z g)
    (c : A3Configuration z g) (dy : IntersectionData z c.y) :
    Nat.card (normalizer (coreIntersection z g : Set G) ⊓ normalizer (c.A : Set G) ⊓
      normalizer (coreIntersection z c.y : Set G) : Subgroup G) = 64 := by
  rw [inf_right_comm, geometry_endpoint_intersection h d c dy,
    c.normalizer_intersection, card_map_of_injective (Centralizer z).subtype_injective,
    h.centralizer_sylow_two_card]

theorem configuration_ambient_parabolics (h : Hypotheses z) (d : IntersectionData z g)
    (c : A3Configuration z g) (dy : IntersectionData z c.y)
    (hpoint : Nat.card (normalizer (coreIntersection z g : Set G) ⊓
      normalizer (c.A : Set G) : Subgroup G) = 192)
    (hplane : Nat.card (normalizer (coreIntersection z c.y : Set G) ⊓
      normalizer (c.A : Set G) : Subgroup G) = 192) :
    let M := normalizer (coreIntersection z g : Set G)
    let K := normalizer (c.A : Set G)
    let R := normalizer (coreIntersection z c.y : Set G)
    let B := M ⊓ K ⊓ R
    Quasithin.I5.RankTwoParabolics M (B.subgroupOf M) (K.subgroupOf M) (R.subgroupOf M) ∧
    Quasithin.I5.RankTwoParabolics K (B.subgroupOf K) (M.subgroupOf K) (R.subgroupOf K) ∧
    Quasithin.I5.RankTwoParabolics R (B.subgroupOf R) (M.subgroupOf R) (K.subgroupOf R) := by
  dsimp only
  have hB := configuration_triple_card h d c dy
  have hMR : Nat.card (normalizer (coreIntersection z g : Set G) ⊓
      normalizer (coreIntersection z c.y : Set G) : Subgroup G) = 192 := by
    rw [geometry_endpoint_intersection h d c dy, h.centralizer_card]
  refine ⟨?_, ?_, ?_⟩
  · exact Parabolics.pair_parabolics_PSL _ _ _ _ inferInstance
      ((IsPGroup.of_card (p := 2) (n := 3) d.card).of_equiv
        (subgroupOfEquivOfLe (coreIntersection z g).le_normalizer).symm)
      d.normalizer_quotient (intersection_normalizer_card d) hpoint hMR hB
  · simpa only [inf_comm (normalizer (c.A : Set G))] using
      Parabolics.pair_parabolics_product (normalizer (c.A : Set G))
        (normalizer (coreIntersection z g : Set G))
        (normalizer (coreIntersection z c.y : Set G)) c.A inferInstance
        ((IsPGroup.of_card (p := 2) (n := 4) c.card).of_equiv
          (subgroupOfEquivOfLe c.A.le_normalizer).symm)
        c.normalizer_quotient (configuration_normalizer_card c)
        (by rwa [inf_comm]) (by rwa [inf_comm])
        (by simpa only [inf_comm (normalizer (c.A : Set G))] using hB)
  · have he : normalizer (coreIntersection z c.y : Set G) ⊓
        normalizer (coreIntersection z g : Set G) ⊓ normalizer (c.A : Set G) =
        normalizer (coreIntersection z g : Set G) ⊓ normalizer (c.A : Set G) ⊓
        normalizer (coreIntersection z c.y : Set G) := by ac_rfl
    simpa only [he] using
      Parabolics.pair_parabolics_PSL (normalizer (coreIntersection z c.y : Set G))
        (normalizer (coreIntersection z g : Set G)) (normalizer (c.A : Set G))
        (coreIntersection z c.y) inferInstance
        ((IsPGroup.of_card (p := 2) (n := 3) dy.card).of_equiv
          (subgroupOfEquivOfLe (coreIntersection z c.y).le_normalizer).symm)
        dy.normalizer_quotient (intersection_normalizer_card dy)
        (by rwa [inf_comm]) hplane (by rwa [he])

theorem configuration_parabolics_of_overlap_card (h : Hypotheses z)
    (d : IntersectionData z g) (c : A3Configuration z g) (dy : IntersectionData z c.y)
    (hpoint : Nat.card (normalizer (coreIntersection z g : Set G) ⊓
      normalizer (c.A : Set G) : Subgroup G) = 192)
    (hplane : Nat.card (normalizer (coreIntersection z c.y : Set G) ⊓
      normalizer (c.A : Set G) : Subgroup G) = 192) : A3ParabolicData z g c.y c.A := by
  obtain ⟨hp, hl, hr⟩ := configuration_ambient_parabolics h d c dy hpoint hplane
  have hK : normalizer (c.A : Set G) ≤ geometryGroup z g c.y :=
    Parabolics.middle_le_of_generate _ _ _ _ le_sup_left le_sup_right hl.generate
  have hB : Quasithin.I5.chamberSubgroup (geometryFamily z g c.y c.A) =
      (normalizer (coreIntersection z g : Set G) ⊓ normalizer (c.A : Set G) ⊓
        normalizer (coreIntersection z c.y : Set G)).subgroupOf (geometryGroup z g c.y) := by
    ext x
    simp only [Quasithin.I5.chamberSubgroup, mem_iInf]
    constructor
    · intro hx; exact ⟨⟨hx 0, hx 1⟩, hx 2⟩
    · intro hx i; fin_cases i
      · exact hx.1.1
      · exact hx.1.2
      · exact hx.2
  refine ⟨hK, ?_, ?_, ?_⟩
  · rw [hB]
    exact Parabolics.rankTwo_subgroupOf _ _ _ _ _ le_sup_left hp
  · rw [hB]
    exact Parabolics.rankTwo_subgroupOf _ _ _ _ _ hK hl
  · rw [hB]
    exact Parabolics.rankTwo_subgroupOf _ _ _ _ _ le_sup_right hr

/-- The first endpoint overlap is the stabilizer of the actual plane A ∩ E.
The split-model normalizer theorem discharges the model premise of marked
transport, giving the order asserted in source Lemma 3.2. -/
theorem configuration_point_geometry (d : IntersectionData z g)
    (c : A3Configuration z g) :
    Nat.card (normalizer (coreIntersection z g : Set G) ⊓
      normalizer (c.A : Set G) : Subgroup G) = 192 ∧
    Nat.card (c.A ⊓ coreIntersection z g : Subgroup G) = 4 ∧
    normalizer (coreIntersection z g : Set G) ⊓ normalizer (c.A : Set G) =
      normalizer (coreIntersection z g : Set G) ⊓
        normalizer ((c.A ⊓ coreIntersection z g : Subgroup G) : Set G) :=
  Parabolics.MarkedTransport.point_geometry d c
    Matrix.PSL3Two.SplitParabolic.elementary_sixteen_normalizer_geometry

/-- The second endpoint overlap is the stabilizer of the actual plane A ∩ F,
with its order and the order of that plane proved in the same marked model. -/
theorem configuration_plane_geometry (c : A3Configuration z g)
    (dy : IntersectionData z c.y) :
    Nat.card (normalizer (coreIntersection z c.y : Set G) ⊓
      normalizer (c.A : Set G) : Subgroup G) = 192 ∧
    Nat.card (c.A ⊓ coreIntersection z c.y : Subgroup G) = 4 ∧
    normalizer (coreIntersection z c.y : Set G) ⊓ normalizer (c.A : Set G) =
      normalizer (coreIntersection z c.y : Set G) ⊓
        normalizer ((c.A ⊓ coreIntersection z c.y : Subgroup G) : Set G) :=
  Parabolics.MarkedTransport.plane_geometry c dy
    Matrix.PSL3Two.SplitParabolic.elementary_sixteen_normalizer_geometry

/-- All three literal rank-two parabolic pairs of source Lemma 3.2, including
containment of N_G(A) in the group generated by the endpoint normalizers.
The marked split calculation supplies both overlap orders. -/
theorem configuration_parabolics (h : Hypotheses z) (d : IntersectionData z g)
    (c : A3Configuration z g) (dy : IntersectionData z c.y) :
    A3ParabolicData z g c.y c.A :=
  configuration_parabolics_of_overlap_card h d c dy
    (configuration_point_geometry d c).1 (configuration_plane_geometry c dy).1

/-- Apply the parabolic theorem to the source family of local intersections.
Only the earlier configuration construction remains an explicit input. -/
theorem configuration_parabolics_of_local_intersections (h : Hypotheses z)
    (local_intersections : ∀ y : G, y * z * y⁻¹ ∈ coreInG z → y * z * y⁻¹ ≠ z →
      IntersectionData z y)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (c : A3Configuration z g) : A3ParabolicData z g c.y c.A :=
  configuration_parabolics h (local_intersections g hgQ hg) c
    (local_intersections c.y c.conjugate_mem c.conjugate_ne)

/-- The thirteen-element fusion count and the actual A₃-system, with the
parabolic input discharged. The source Lemma 3.1 configuration must still
be constructed by the geometry assembly owner. -/
theorem geometry_of_split_configuration (h : Hypotheses z)
    (local_intersections : ∀ y : G, y * z * y⁻¹ ∈ coreInG z → y * z * y⁻¹ ≠ z →
      IntersectionData z y)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (c : A3Configuration z g) :
    Nat.card (CoreFusion z) = 13 ∧
      ∃ L : Subgroup G, Centralizer z ≤ L ∧ Nonempty (Quasithin.I5.DSystem .A3 L) := by
  have d := local_intersections g hgQ hg
  have dy := local_intersections c.y c.conjugate_mem c.conjugate_ne
  have p := configuration_parabolics_of_local_intersections h local_intersections hgQ hg c
  exact ⟨configuration_fusion_card h d c dy, geometryGroup z g c.y,
    geometry_centralizer_le d c.y, ⟨configuration_system h d c dy p⟩⟩


/-- Apply the overlap calculation to the original fusion and D-system
consumer. The two cardinal premises must be supplied by the marked endpoint
geometry before this yields the source theorem. -/
theorem geometry_of_endpoint_overlap_cards (h : Hypotheses z)
    (local_intersections : ∀ y : G, y * z * y⁻¹ ∈ coreInG z → y * z * y⁻¹ ≠ z →
      IntersectionData z y)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (c : A3Configuration z g)
    (hpoint : Nat.card (normalizer (coreIntersection z g : Set G) ⊓
      normalizer (c.A : Set G) : Subgroup G) = 192)
    (hplane : Nat.card (normalizer (coreIntersection z c.y : Set G) ⊓
      normalizer (c.A : Set G) : Subgroup G) = 192) :
    Nat.card (CoreFusion z) = 13 ∧
      ∃ L : Subgroup G, Centralizer z ≤ L ∧ Nonempty (Quasithin.I5.DSystem .A3 L) := by
  have d := local_intersections g hgQ hg
  have dy := local_intersections c.y c.conjugate_mem c.conjugate_ne
  have p := configuration_parabolics_of_overlap_card h d c dy hpoint hplane
  exact ⟨configuration_fusion_card h d c dy, geometryGroup z g c.y,
    geometry_centralizer_le d c.y, ⟨configuration_system h d c dy p⟩⟩

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition

end

module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.AbelianLinearAction
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.NormalizerFusion
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The point-orbit contradiction excluding E₂₇

The ambient normalizer acts on the original order-three subgroups of R.
The stabilizer of B is exactly N_G(B) intersected with N_G(R), whose
order is 27·16 by the constructed product R T_R. In the abelian branch,
normalizer fusion puts the four-orbit point C_R(f) in the B-orbit.
The exhaustive 1,4,8 partition makes this full orbit have size 5 or 13.
The faithful GL₃(3) action excludes size 5, forcing index 13 and quotient
order 16·13. The proved linear-group obstruction excludes that order.

Using the exhaustive partition directly removes the need for the
source's separate parity argument. No Sylow promotion or nonabelian
structure is assumed in the exclusion.

Source: Aschbacher–Smith, final paragraph of J.2.7, printed p.437 (PDF p.448).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
open Subgroup LocalAction LocalAction.PointOrbits
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)
variable {hB : Nat.card c.B = 3}
variable {e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))}
variable (D : LocalAction.Data c hB e)

/-- The full normalizer acts on actual order-three subgroups of R. -/
instance normalizerPointsAction (R : Sylow 3 c.NB) :
    MulAction (normalizer (ambient c R : Set G)) (Points c R) :=
  OrderPoints.action (ambient c R).normalizerMonoidHom

theorem normalizer_point_image (R : Sylow 3 c.NB)
    (g : normalizer (ambient c R : Set G)) (U : Points c R) :
    (g • U).val.map (ambient c R).subtype =
      (U.val.map (ambient c R).subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  change (U.val.map ((ambient c R).normalizerMonoidHom g).toMonoidHom).map _ = _
  rw [map_map, map_map]
  rfl

/-- Restriction to the original T_R is precisely the previously constructed action. -/
theorem normalizer_point_restrict (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (t : TR c R Tplus) (U : Points c R) :
    (inclusion (TR_le_normalizer c R Tplus) t) • U = t • U := rfl

/-- The full-normalizer point stabilizer is its literal intersection with N_G(B). -/
theorem basePoint_stabilizer :
    MulAction.stabilizer (normalizer (ambient c D.R : Set G)) (basePoint c hB D.R) =
      c.NB.subgroupOf (normalizer (ambient c D.R : Set G)) := by
  ext g
  change g • basePoint c hB D.R = basePoint c hB D.R ↔ (g : G) ∈ c.NB
  change _ ↔ (g : G) ∈ normalizer (c.B : Set G)
  rw [mem_normalizer_iff_map_conj_eq]
  constructor
  · intro hg
    have hh := congrArg (fun U : Points c D.R => U.val.map (ambient c D.R).subtype) hg
    rw [normalizer_point_image] at hh
    simpa only [basePoint, map_subgroupOf_eq_of_le D.base_le, MulEquiv.toMonoidHom_eq_coe] using hh
  · intro hg
    apply Subtype.ext
    apply map_injective (ambient c D.R).subtype_injective
    rw [normalizer_point_image]
    simpa only [basePoint, map_subgroupOf_eq_of_le D.base_le, MulEquiv.toMonoidHom_eq_coe] using hg

/-- The stabilizer has order 27*16, using the actual disjoint product R T_R. -/
theorem normalizer_intersection_card :
    Nat.card ↥(c.NB ⊓ normalizer (ambient c D.R : Set G)) = 27 * 16 := by
  have he : c.NB ⊓ normalizer (ambient c D.R : Set G) = ambient c D.R ⊔ TR c D.R D.Tplus := by
    apply SetLike.coe_injective
    rw [D.normalizer_product, coe_mul_of_right_le_normalizer_left _ _ (TR_le_normalizer c D.R D.Tplus)]
  have hd : Disjoint (ambient c D.R) (TR c D.R D.Tplus) :=
    (ambient_isPGroup c D.R).disjoint_of_coprime (TR_isPGroup c D.R D.Tplus) (by decide)
  rw [he, card_sup_eq_mul_of_normalizes_of_disjoint _ _ (TR_le_normalizer c D.R D.Tplus) hd,
    D.r_card, D.tr_card]

/-- In the abelian branch the four-orbit point is conjugate to B by N_G(R). -/
theorem fixedPoint_mem_normalizer_orbit (hc : IsMulCommutative (ambient c D.R)) :
    fixedPoint c D.R D.Tplus D.f D.fixed_card ∈
      MulAction.orbit (normalizer (ambient c D.R : Set G)) (basePoint c hB D.R) := by
  obtain ⟨g, hg⟩ := fixed_fusion_in_normalizer c D hc
  have he : g • fixedPoint c D.R D.Tplus D.f D.fixed_card = basePoint c hB D.R := by
    apply Subtype.ext
    apply map_injective (ambient c D.R).subtype_injective
    rw [normalizer_point_image, fixedPoint_image]
    exact hg.trans (map_subgroupOf_eq_of_le D.base_le).symm
  exact ⟨g⁻¹, by simpa only [← he] using inv_smul_smul g (fixedPoint c D.R D.Tplus D.f D.fixed_card)⟩

/-- The full-normalizer B-orbit is either the 1+4 union or all thirteen points. -/
theorem basePoint_normalizer_orbit_card (hc : IsMulCommutative (ambient c D.R)) :
    Nat.card (MulAction.orbit (normalizer (ambient c D.R : Set G)) (basePoint c hB D.R)) = 5 ∨
    Nat.card (MulAction.orbit (normalizer (ambient c D.R : Set G)) (basePoint c hB D.R)) = 13 := by
  classical
  let : Finite (Points c D.R) := inferInstanceAs (Finite {U : Subgroup (ambient c D.R) // Nat.card U = 3})
  obtain ⟨_, _, hbase, hbaseCard, hfixedCard, _, _, U, hUCard,
    hdisBF, _, _, hcover⟩ := D.abelian_points hc
  let N := normalizer (ambient c D.R : Set G)
  let B := basePoint c hB D.R
  let F := fixedPoint c D.R D.Tplus D.f D.fixed_card
  let O := MulAction.orbit N B
  have closed {v : Points c D.R} (hv : v ∈ O) : MulAction.orbit (TR c D.R D.Tplus) v ⊆ O := by
    rintro w ⟨t, rfl⟩
    obtain ⟨g, rfl⟩ := hv
    exact ⟨inclusion (TR_le_normalizer c D.R D.Tplus) t * g, mul_smul _ _ _⟩
  have hBO : MulAction.orbit (TR c D.R D.Tplus) B ⊆ O := closed (MulAction.mem_orbit_self _)
  have hFO : MulAction.orbit (TR c D.R D.Tplus) F ⊆ O :=
    closed (fixedPoint_mem_normalizer_orbit c D hc)
  by_cases hU : U ∈ O
  · right
    have hOU : O = Set.univ := by
      apply Set.Subset.antisymm (Set.subset_univ _)
      rw [← hcover]
      exact Set.union_subset (Set.union_subset hBO hFO) (closed hU)
    rw [show MulAction.orbit N B = O from rfl, hOU, Nat.card_coe_set_eq, Set.ncard_univ]
    exact (D.abelian_points hc).2.1
  · left
    have hO : O = MulAction.orbit (TR c D.R D.Tplus) B ∪
        MulAction.orbit (TR c D.R D.Tplus) F := by
      apply Set.Subset.antisymm ?_ (Set.union_subset hBO hFO)
      intro v hv
      have hvall : v ∈ (MulAction.orbit (TR c D.R D.Tplus) B ∪
          MulAction.orbit (TR c D.R D.Tplus) F) ∪ MulAction.orbit (TR c D.R D.Tplus) U := by
        rw [hcover]
        trivial
      rcases hvall with h | ⟨t, ht⟩
      · exact h
      · exfalso
        apply hU
        have hh := closed hv
        apply hh
        exact ⟨t⁻¹, by simpa only [← ht] using inv_smul_smul t U⟩
    rw [show MulAction.orbit N B = O from rfl, hO, Nat.card_coe_set_eq,
      Set.ncard_union_eq hdisBF, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      hbaseCard, hfixedCard]


/-- Orbit-stabilizer and the literal R T_R product give the quotient order. -/
theorem normalizer_quotient_card_eq_sixteen_mul_orbit :
    Nat.card (AmbientNormalizerQuotient c D.R) = 16 *
      Nat.card (MulAction.orbit (normalizer (ambient c D.R : Set G)) (basePoint c hB D.R)) := by
  let N := normalizer (ambient c D.R : Set G)
  let S := MulAction.stabilizer N (basePoint c hB D.R)
  have hS : Nat.card S = 27 * 16 := by
    dsimp [S]
    rw [basePoint_stabilizer]
    rw [Nat.card_congr ((c.NB.subgroupOf N).equivMapOfInjective
      N.subtype N.subtype_injective).toEquiv, subgroupOf_map_subtype]
    exact normalizer_intersection_card c D
  have hR : Nat.card ((ambient c D.R).subgroupOf N) = 27 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show ambient c D.R ≤ N from le_normalizer)).toEquiv).trans
      D.r_card
  have hprod := card_eq_card_quotient_mul_card_subgroup ((ambient c D.R).subgroupOf N)
  rw [hR] at hprod
  have horbit : Nat.card (MulAction.orbit N (basePoint c hB D.R)) * (27 * 16) = Nat.card N := by
    rw [← hS, ← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N (basePoint c hB D.R))
  change Nat.card N = Nat.card (AmbientNormalizerQuotient c D.R) * 27 at hprod
  change Nat.card (AmbientNormalizerQuotient c D.R) =
    16 * Nat.card (MulAction.orbit N (basePoint c hB D.R))
  omega


/-- The 1,4,8 orbits and the absence of a factor five force normalizer index 13. -/
theorem abelian_normalizer_index_thirteen (hc : IsMulCommutative (ambient c D.R)) :
    (c.NB.subgroupOf (normalizer (ambient c D.R : Set G))).index = 13 := by
  rw [← basePoint_stabilizer c D, MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
  rcases basePoint_normalizer_orbit_card c D hc with h | h
  · have horder := normalizer_quotient_card_eq_sixteen_mul_orbit c D
    rw [h] at horder
    exact (abelian_normalizer_quotient_not_five c D hc (by rw [horder]; decide)).elim
  · exact h

/-- The elementary-abelian branch is impossible in the original ambient group. -/
theorem not_commutative : ¬ IsMulCommutative (ambient c D.R) := by
  intro hc
  apply abelian_normalizer_quotient_ne_208 c D hc
  have hi := abelian_normalizer_index_thirteen c D hc
  rw [← basePoint_stabilizer c D, MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at hi
  rw [normalizer_quotient_card_eq_sixteen_mul_orbit, hi]

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow

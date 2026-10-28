module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.CoreOrders
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.NeighborKernels
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The original A₃ point residue and pair cores

The PSL₃(2) quotient marks the two actual point parabolics. It identifies
incident lines and planes with the Fano plane, retaining literal cosets and
incidence. The irreducible four-group in the point parabolic and the order-two
core in the line parabolic give the source point-line core product.

Source: Aschbacher–Smith I.5.4 and I.5.7, printed pp.420–421.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .A3 G)

theorem a3_point_standard_quotientMark :
    ∃ e : (S.family 0 ⧸ pCore 2 (S.family 0)) ≃* Matrix.PSL3Two.PSL,
      ((localParabolic S.family 0 1).map (S.localQuotientMap 0 e) =
          Matrix.PSL3Two.pointParabolic ∧
        (localParabolic S.family 0 2).map (S.localQuotientMap 0 e) =
          Matrix.PSL3Two.lineParabolic) ∨
      ((localParabolic S.family 0 1).map (S.localQuotientMap 0 e) =
          Matrix.PSL3Two.lineParabolic ∧
        (localParabolic S.family 0 2).map (S.localQuotientMap 0 e) =
          Matrix.PSL3Two.pointParabolic) := by
  obtain ⟨e⟩ := S.point_A3 rfl
  apply S.exists_standard_quotientMark 0 1 2 S.point_parabolics e
  intro T
  obtain ⟨g, _, _, _, h⟩ := Matrix.PSL3Two.Fano.sylow_parabolics_conjugate T
  exact ⟨g, h⟩

structure A3PointResidue (x : S.Point) where
  lines : Matrix.PSL3Two.Fano.Point ≃ {l : S.Line // S.Inc x l}
  planes : Matrix.PSL3Two.Fano.Line ≃ {π : S.Plane // S.Inc x π}
  incident : ∀ p l, S.Inc (lines p).val (planes l).val ↔ Matrix.PSL3Two.Fano.Incident p l

theorem exists_a3_basePointResidue : Nonempty (S.A3PointResidue S.basePoint) := by
  obtain ⟨e, he⟩ := S.a3_point_standard_quotientMark
  let f := S.localQuotientMap 0 e
  have hker := S.localQuotientMap_ker_le 0 e
  have hkP : f.ker ≤ localParabolic S.family 0 1 :=
    hker.trans (S.point_parabolics.borel_eq ▸ inf_le_left)
  have hkL : f.ker ≤ localParabolic S.family 0 2 :=
    hker.trans (S.point_parabolics.borel_eq ▸ inf_le_right)
  obtain ⟨m⟩ := Matrix.PSL3Two.Fano.exists_quotientMark
    (localParabolic S.family 0 1) (localParabolic S.family 0 2) f
    (S.localQuotientMap_surjective 0 e) hkP hkL he
  refine ⟨⟨m.points.symm.trans (S.pointedCosetEquiv 0 1 (by decide)),
    m.lines.symm.trans (S.pointedCosetEquiv 0 2 (by decide)), ?_⟩⟩
  intro p l
  change S.Inc (S.pointedCosetEquiv 0 1 _ (m.points.symm p)).val
    (S.pointedCosetEquiv 0 2 _ (m.lines.symm l)).val ↔ _
  rw [← S.pointedCosetEquiv_incident 0 1 2, m.incident,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem exists_a3_pointResidue (x : S.Point) : Nonempty (S.A3PointResidue x) := by
  obtain ⟨m⟩ := S.exists_a3_basePointResidue
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S.basePoint x
  refine ⟨⟨m.lines.trans (S.incidentFiberTranslation 0 1 _ g),
    m.planes.trans (S.incidentFiberTranslation 0 2 _ g), ?_⟩⟩
  intro p l
  change S.Inc (g • (m.lines p).val) (g • (m.planes l).val) ↔ _
  rw [← m.incident]
  constructor
  · intro h
    simpa only [inv_smul_smul] using h.smul S g⁻¹
  · exact fun h => h.smul S g

theorem a3_point_lines_card (x : S.Point) : Nat.card {l : S.Line // S.Inc x l} = 7 := by
  obtain ⟨m⟩ := S.exists_a3_pointResidue x
  rw [← Nat.card_congr m.lines, Nat.card_eq_fintype_card, Matrix.PSL3Two.Fano.card_point]

theorem a3_point_planes_card (x : S.Point) : Nat.card {π : S.Plane // S.Inc x π} = 7 := by
  obtain ⟨m⟩ := S.exists_a3_pointResidue x
  rw [← Nat.card_congr m.planes, Nat.card_eq_fintype_card, Matrix.PSL3Two.Fano.card_line]

theorem a3_point_line_parabolic_normalCore :
    (localParabolic S.family 0 1).normalCore = pCore 2 (S.family 0) := by
  obtain ⟨e, he⟩ := S.a3_point_standard_quotientMark
  have hk : (S.localQuotientMap 0 e).ker ≤ localParabolic S.family 0 1 :=
    (S.localQuotientMap_ker_le 0 e).trans
      (S.point_parabolics.borel_eq ▸ inf_le_left)
  exact (Matrix.PSL3Two.Fano.normalCore_eq_ker_of_standard_parabolic
    (localParabolic S.family 0 1) (S.localQuotientMap 0 e)
    (S.localQuotientMap_surjective 0 e) hk (he.imp And.left And.left)).trans
      (S.localQuotientMap_ker 0 e)

private theorem digon_core_card (U : Subgroup SymmetricThreeProduct.G)
    (h : U = SymmetricThreeProduct.leftParabolic ∨ U = SymmetricThreeProduct.rightParabolic) :
    Nat.card (pCore 2 U) = 2 := by
  rcases h with rfl | rfl
  · rw [SymmetricThreeProduct.left_twoCore]
    exact SymmetricThreeProduct.card_ker_leftQuotientMap
  · rw [SymmetricThreeProduct.right_twoCore]
    exact SymmetricThreeProduct.card_ker_rightQuotientMap

private theorem linear_core_data (U : Subgroup Matrix.PSL3Two.PSL)
    (h : U = Matrix.PSL3Two.pointParabolic ∨ U = Matrix.PSL3Two.lineParabolic) :
    Nat.card (pCore 2 U) = 4 ∧
      ∀ N : Subgroup U, N.Normal → N ≤ pCore 2 U → N = ⊥ ∨ N = pCore 2 U := by
  rcases h with rfl | rfl
  · refine ⟨Matrix.PSL3Two.pointParabolic_core_data.2, ?_⟩
    intro N hn hN
    let := hn
    exact Matrix.PSL3Two.pointParabolic_normal_le_core N hN
  · refine ⟨Matrix.PSL3Two.lineParabolic_core_data.2, ?_⟩
    intro N hn hN
    let := hn
    exact Matrix.PSL3Two.lineParabolic_normal_le_core N hN

theorem a3_point_line_core_join : (S.pair 0 1).pCoreIn 2 = S.Q 0 ⊔ S.Q 1 := by
  obtain ⟨e, he⟩ := S.a3_point_standard_quotientMark
  obtain ⟨d, hd⟩ := S.line_standard_quotientMark
  have hlin := linear_core_data _ (he.imp And.left And.left)
  have htwo := digon_core_card _ (hd.imp And.left And.left)
  exact S.pair_core_join_of_local_models 0 1 e d hlin.1 htwo hlin.2

theorem a3_line_pair_core_card (j : Fin 3) (hj : j = 0 ∨ j = 2) :
    Nat.card ((S.pair 1 j).pCoreIn 2) = Nat.card (S.Q 1) * 2 := by
  obtain ⟨e, he⟩ := S.line_standard_quotientMark
  rw [S.pair_core_card 1 j e]
  congr 1
  apply digon_core_card
  rcases hj with rfl | rfl
  · exact he.imp And.left And.left
  · exact he.symm.imp And.right And.right

theorem a3_core_card_product (i j : Fin 3) :
    Nat.card (S.Q i) * Nat.card (S.Q j) =
      Nat.card (S.Q i ⊓ S.Q j : Subgroup G) * Nat.card (S.Q i ⊔ S.Q j : Subgroup G) := by
  let : Finite S.T := Finite.of_injective (inclusion (S.T_le 0)) (inclusion_injective _)
  have hn : (S.Q j).subgroupOf S.T ≤ normalizer ((S.Q i).subgroupOf S.T) := by
    intro a ha
    apply (S.Q i).le_normalizer_comap S.T.subtype
    exact S.family_le_normalizer_Q i (S.T_le i (S.Q_le_T j ha))
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    ((S.Q i).subgroupOf S.T) ((S.Q j).subgroupOf S.T) hn
  rw [← subgroupOf_sup (S.Q_le_T i) (S.Q_le_T j)] at h
  change Nat.card ((S.Q i).subgroupOf S.T) * Nat.card ((S.Q j).subgroupOf S.T) =
    Nat.card ((S.Q i ⊓ S.Q j).subgroupOf S.T) *
      Nat.card ((S.Q i ⊔ S.Q j).subgroupOf S.T) at h
  simpa only [Nat.card_congr (subgroupOfEquivOfLe (S.Q_le_T i)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (S.Q_le_T j)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans (S.Q_le_T i))).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (sup_le (S.Q_le_T i) (S.Q_le_T j))).toEquiv] using h

end Quasithin.I5.DSystem

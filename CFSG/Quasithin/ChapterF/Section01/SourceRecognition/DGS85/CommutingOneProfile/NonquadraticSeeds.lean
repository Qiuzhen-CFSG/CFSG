module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearCentralLayers

/-!
# Nonquadratic seed action and the nonabelian Chapter 11 pair span

The proved opposite-seed supplement identifies the fixed subgroup of that
seed on Z_alpha with Z_beta. If the seed acted quadratically, its whole
displacement on Z_alpha would therefore lie in Z_beta. The pair-core
identity then gives [Q_beta,Z_alpha] <= Z_beta. Both neighboring centers
centralize this displacement, so the characteristic-two quadratic-actor
lemma makes their join a two-group. This contradicts their proved distinct
fixed neighbors. Thus the seed action is not quadratic.

If the pair span were abelian, the elementary first seed would centralize
the opposite seed and make that action quadratic. Its derived subgroup is
therefore nontrivial. This supplies (11.3)(e,f) after the independently proved
(11.3)(h)--(11.5) core identities, without any new module-recognition premise.
The alpha linear marking and earlier local data remain explicit; every beta
catalogue row is retained. Source: Delgado--Goldschmidt--Stellmacher,
Groups and Graphs (1985), (11.3)(e,f), pp.169--170; (11.5), p.172.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

private theorem pair_two_group_of_central_displacement (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (hdisp : ⁅Q (family P) b,Z (family P) a⁆ ≤ Z (family P) b)
    (hZba : Z (family P) b ≤ Z (family P) a)
    (hZbc : Z (family P) b ≤ Z (family P) c) :
    IsPGroup 2 (Z (family P) a ⊔ Z (family P) c : Subgroup G) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let M := stabilizer (family P) b
  let A := (Z (family P) a).subgroupOf M
  let C := (Z (family P) c).subgroupOf M
  let E := (Z (family P) b).subgroupOf M
  have haM : Z (family P) a ≤ M :=
    (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans (source_Z_Q_U h a).2).trans
      ((ballKernel_one_le_edge _ hab).trans inf_le_right)
  have hcM : Z (family P) c ≤ M :=
    (((source_Z_Q_U h c).1.trans (map_subtype_le _)).trans (source_Z_Q_U h c).2).trans
      ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.subgroupOf hcM
  have hcomm : ⁅pCore 2 M,A⁆ ≤ E := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le haM,
      map_subgroupOf_eq_of_le (Z_le_stabilizer _ b)]
    exact hdisp
  have hAE : A ≤ centralizer (E : Set M) := by
    intro x hx y hy
    apply Subtype.ext
    exact (le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative (Z (family P) a))) hx y.val (hZba hy)
  have hCE : C ≤ centralizer (E : Set M) := by
    intro x hx y hy
    apply Subtype.ext
    exact (le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative (Z (family P) c))) hx y.val (hZbc hy)
  have hp := isPGroup_sup_of_centralized_displacement (pCore 2 M) A C E
    (pCore_isPGroup (p := 2)) (IsElementaryAbelian.isPGroup 2 C)
    le_normalizer_of_normal le_normalizer_of_normal
    (inf_le_right.trans (source_vertex_core_selfCentralizing h b)) hcomm hAE hCE
  rw [←subgroupOf_sup haM hcM] at hp
  exact hp.of_equiv (subgroupOfEquivOfLe (sup_le haM hcM))

/-- The opposite seed does not act quadratically on the alpha center.
This is source (11.3)(f), using the proved core identities of the linear branch. -/
theorem source_linear_rankOne_seed_nonquadratic (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    ⁅⁅Z (family P) a,Z (family P) c ⊓ Q (family P) b⁆,
      Z (family P) c ⊓ Q (family P) b⁆ ≠ ⊥ := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let C := Z (family P) c ⊓ Q (family P) b
  let E := ⁅Z (family P) a,C⁆
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨hp,hcore⟩ := source_linear_rankOne_core_identities h hB d hc hb hbc hac Ma Mb ea
  have hsupp : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      C ⊔ Q (family P) a := by
    rw [sup_comm]
    exact alpha_supplement_of_pair_generation _ _ _ _ _ hp hcore
      ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  have hZa : E ≤ Z (family P) a :=
    le_normalizer_iff_commutator_le_left.mp
      (inf_le_right.trans (source_adjacent_core_normalizes_center h hab))
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le hZa
  intro hquad
  have hEb : E ≤ Z (family P) b := by
    apply source_elementary_central_edge_le_center h hB d hab E
    · rw [hsupp]
      exact (hZa.trans ((source_Z_Q_U h a).1.trans (map_subtype_le _))).trans le_sup_right
    · rw [hsupp]
      apply le_centralizer_iff.mpr
      apply sup_le
      · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hquad)
      · exact (source_core_centralizes_center h a).trans (centralizer_le hZa)
  have hQdisp : ⁅Q (family P) b,Z (family P) a⁆ ≤ Z (family P) b := by
    rw [hcore]
    have hn : Q (family P) b ≤ normalizer (Z (family P) b : Set G) :=
      (source_core_centralizes_center h b).trans (Subgroup.centralizer_le_normalizer _)
    apply commutator_sup_le_of_relative_normal (Q (family P) b)
      _ _ _ (Z (family P) b) hn (pairSpan_le_core _ _ _) inf_le_right
    · apply commutator_sup_le_of_relative_normal (Q (family P) b)
        _ _ _ (Z (family P) b) hn inf_le_right inf_le_right
      · exact (commutator_eq_bot_iff_le_centralizer.mpr
          (inf_le_left.trans (le_centralizer_iff_isMulCommutative.mpr
            (inferInstance : IsMulCommutative (Z (family P) a))))).le.trans bot_le
      · rw [commutator_comm]
        exact hEb
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (inf_le_left.trans (source_core_centralizes_center h a))).le.trans bot_le
  have hi := (source_linear_rankOne_center_intersections h hB d hc hb hcomm hbc hac Ma Mb ea).2.2.1
  exact source_rankOne_centers_not_isPGroup h hB d hc hb hbc hac Mb
    (pair_two_group_of_central_displacement h hab hbc hQdisp
      (hi.ge.trans inf_le_left) (hi.ge.trans inf_le_right))

/-- The actual two-seed group is nonabelian, as in (11.3)(e). -/
theorem source_linear_rankOne_pair_nonabelian (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    ⁅V,V⁆ ≠ ⊥ := by
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  change ⁅V,V⁆ ≠ ⊥
  intro he
  apply source_linear_rankOne_seed_nonquadratic h hB d hc hb hcomm hbc hac Ma Mb ea
  have hab := source_critical_one_adjacent hc hb
  have hZaM : Z (family P) a ≤ stabilizer (family P) b :=
    (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans (source_Z_Q_U h a).2).trans
      ((ballKernel_one_le_edge _ hab).trans inf_le_right)
  have hseed : ⁅Z (family P) a,Z (family P) c ⊓ Q (family P) b⁆ ≤
      Z (family P) a ⊓ Q (family P) b := by
    apply le_inf
    · exact le_normalizer_iff_commutator_le_left.mp
        (inf_le_right.trans (source_adjacent_core_normalizes_center h hab))
    · exact (commutator_mono le_rfl inf_le_right).trans
        (le_normalizer_iff_commutator_le_right.mp
          (hZaM.trans (stabilizer_normalizes_Q (family P) b)))
  exact bot_unique ((commutator_mono (hseed.trans le_sup_left) le_sup_right).trans he.le)
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

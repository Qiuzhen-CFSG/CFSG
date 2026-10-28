module

public import Theory.SpecificGroups.BinaryLinear.CubicPairGeometry.Algebra
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.FourComponent
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.TwoNodes.SolvableFlags

/-!
# Common coordinates for two normalized cubic residuals

Let U be a Sylow two-subgroup of GL₄(2) or GL₅(2), normalizing two
2-perfect subgroups A and B. Assume their intrinsic two-core quotients
have order three, and the corresponding quotient of their join has order
nine. The theorems below construct one basis for U and two ordered,
nonadjacent nodes whose parabolics are A U and B U. Their embedded
two-residuals are exactly A and B, and their two-node parabolic is A B U.

The cubic quotient calculation gives index three, so Sylow-overgroup
exhaustion deletes one cut for each mark. Full-flag invariant-subspace
reconstruction aligns all cuts in a single basis. Containment detection
identifies the join's cuts. Its solvability and three-part nine exclude
adjacent nodes: in dimension four an adjacent pair has a PSL₃(2) quotient;
in dimension five the proved diagonal-block classification applies.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed pp.959–960 (PDF pp.976–977), especially the two marked minimal
parabolics and their nonadjacent rank-two join on p.960. These are intrinsic
model theorems; the transport from the source starred groups remains with
the source assembly. No node identification or solvability is assumed.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.PairGeometry

private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem four_overgroup_coordinates (U : Sylow 2 (LinearGroup 4))
    (b : Basis 3) (hb : (U : Subgroup (LinearGroup 4)) = cutStabilizer b Set.univ)
    (P : Subgroup (LinearGroup 4)) (hUP : (U : Subgroup (LinearGroup 4)) ≤ P) :
    ∃ cuts : Set (Fin 3), P = cutStabilizer b cuts := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (LinearGroup 4) Linear.Four.standardSylow U
  have hmap : Linear.Four.standardBorel.map (MulAut.conj g).toMonoidHom =
      (U : Subgroup (LinearGroup 4)) := by
    change ((g • Linear.Four.standardSylow : Sylow 2 (LinearGroup 4)) : Subgroup (LinearGroup 4)) = _
    rw [hg]
  let Q := P.map (MulAut.conj g).symm.toMonoidHom
  have hBQ : Linear.Four.standardBorel ≤ Q := by
    intro u hu
    apply Subgroup.mem_map_equiv.mpr
    apply hUP
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  obtain ⟨cuts, hQ⟩ := Linear.Four.standard_overgroups_of_bruhat
    Linear.Four.hasBruhatDecomposition Q hBQ
  have hQP : Q.map (MulAut.conj g).toMonoidHom = P :=
    (Subgroup.map_symm_eq_iff_map_eq Q (e := MulAut.conj g) (H := P)).mp rfl
  have hc : P = cutStabilizer (Linear.Four.standardBasis.map g) cuts := by
    rw [← hQP, hQ]
    exact cutStabilizer_map_conj _ _ _
  refine ⟨cuts, hc.trans (cutStabilizer_eq_of_fullFlag_le b _ cuts ?_)⟩
  rw [← hc, ← hb]
  exact hUP

private theorem five_overgroup_coordinates (U : Sylow 2 (LinearGroup 5))
    (b : Basis 4) (hb : (U : Subgroup (LinearGroup 5)) = cutStabilizer b Set.univ)
    (P : Subgroup (LinearGroup 5)) (hUP : (U : Subgroup (LinearGroup 5)) ≤ P) :
    ∃ cuts : Set (Fin 4), P = cutStabilizer b cuts := by
  obtain ⟨c, cuts, hc⟩ := FiveFlagGeometry.isFlagParabolic_of_sylow_le U P hUP
  change P = cutStabilizer c cuts at hc
  refine ⟨cuts, hc.trans (cutStabilizer_eq_of_fullFlag_le b c cuts ?_)⟩
  rw [← hc, ← hb]
  exact hUP

/-- The join retains exactly the cuts retained by both parabolics. -/
private theorem join_nodes {m : ℕ} (b : Basis m)
    (hcoords : ∀ P : Subgroup (LinearGroup (m + 1)), cutStabilizer b Set.univ ≤ P →
      ∃ cuts : Set (Fin m), P = cutStabilizer b cuts)
    (i j : Fin m) :
    minimalParabolic b i ⊔ minimalParabolic b j = cutStabilizer b ({i, j} : Set (Fin m))ᶜ := by
  obtain ⟨cuts, hc⟩ := hcoords (minimalParabolic b i ⊔ minimalParabolic b j)
    (((cutStabilizer_le_iff b Set.univ {i}ᶜ).mpr (Set.subset_univ _)).trans le_sup_left)
  have hi : cuts ⊆ ({i} : Set (Fin m))ᶜ :=
    (cutStabilizer_le_iff b _ _).mp (hc ▸ (le_sup_left : minimalParabolic b i ≤ _))
  have hj : cuts ⊆ ({j} : Set (Fin m))ᶜ :=
    (cutStabilizer_le_iff b _ _).mp (hc ▸ (le_sup_right : minimalParabolic b j ≤ _))
  have hle : minimalParabolic b i ⊔ minimalParabolic b j ≤
      cutStabilizer b ({i, j} : Set (Fin m))ᶜ := by
    apply sup_le
    · exact (cutStabilizer_le_iff b _ _).mpr (by simp [Set.subset_def])
    · exact (cutStabilizer_le_iff b _ _).mpr (by simp [Set.subset_def])
  have ht := (cutStabilizer_le_iff b cuts ({i, j} : Set (Fin m))ᶜ).mp (hc ▸ hle)
  have he : cuts = ({i, j} : Set (Fin m))ᶜ := by
    apply Set.Subset.antisymm _ ht
    intro k hk
    have hki := hi hk
    have hkj := hj hk
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff] at *
    tauto
  exact hc.trans (congrArg (cutStabilizer b) he)

private theorem four_pair_endpoints (b : Basis 3) (i j : Fin 3) (hij : i ≠ j)
    (hs : Group.IsSolvable (cutStabilizer b ({i, j} : Set (Fin 3))ᶜ)) :
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) := by
  have hbad (k : Fin 3) : ¬ Group.IsSolvable (fourParabolic b {k, fourAdjacentNode k}) := by
    intro hs'
    let := hs'
    let e := (fourEnlargedQuotientEquiv b k).trans SmallParabolicLevi.linearThreeEquivProjective.symm
    let : Group.IsSolvable (LinearGroup 3) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom.comp (QuotientGroup.mk' _))
        (e.surjective.comp (QuotientGroup.mk'_surjective _))
    let : Group.IsPerfect (LinearGroup 3) := linearGroup_isPerfect 3 (by decide)
    let : Nontrivial (LinearGroup 3) := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [← Nat.card_congr (matrixEquivLinear 3).toEquiv, Matrix.card_GL_field]
      decide
    exact Group.IsPerfect.not_isSolvable (LinearGroup 3) inferInstance
  have h0 := hbad 0
  have h2 := hbad 2
  change Group.IsSolvable (fourParabolic b {i, j}) at hs
  fin_cases i <;> fin_cases j <;> simp_all [fourAdjacentNode]
  · exact h0 hs
  · let := hs
    let e := MulEquiv.subgroupCongr (congrArg (fourParabolic b) (Set.pair_comm (1 : Fin 3) 0))
    exact h0 (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · let := hs
    let e := MulEquiv.subgroupCongr (congrArg (fourParabolic b) (Set.pair_comm (1 : Fin 3) 2))
    exact h2 (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · exact h2 hs

private theorem five_pair_nonadjacent (b : Basis 4) (i j : Fin 4) (hij : i ≠ j)
    (hs : Group.IsSolvable (cutStabilizer b ({i, j} : Set (Fin 4))ᶜ))
    (h3 : (Nat.card (cutStabilizer b ({i, j} : Set (Fin 4))ᶜ)).factorization 3 = 2) :
    i.val + 1 < j.val ∨ j.val + 1 < i.val := by
  obtain ⟨k, l, hkl, hn, he⟩ := fiveParabolic_nodes_eq_pair_of_solvable_three_part b {i,j} hs h3
  have hi : i = k ∨ i = l := by have := Set.ext_iff.mp he i; simp at this; tauto
  have hj : j = k ∨ j = l := by have := Set.ext_iff.mp he j; simp at this; tauto
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp_all [or_comm]

private theorem marked_nodes {m : ℕ} (U : Sylow 2 (LinearGroup (m + 1)))
    (A B : Subgroup (LinearGroup (m + 1)))
    (ha : IsPPerfect 2 A) (hb : IsPPerfect 2 B)
    (hna : (U : Subgroup (LinearGroup (m + 1))) ≤ normalizer (A : Set _))
    (hnb : (U : Subgroup (LinearGroup (m + 1))) ≤ normalizer (B : Set _))
    (hca : Nat.card (A ⧸ pCore 2 A) = 3) (hcb : Nat.card (B ⧸ pCore 2 B) = 3)
    (hcab : Nat.card ((A ⊔ B : Subgroup _) ⧸ pCore 2 (A ⊔ B : Subgroup _)) = 9)
    (b : Basis m) (hu : (U : Subgroup _) = cutStabilizer b Set.univ)
    (hcoords : ∀ P : Subgroup (LinearGroup (m + 1)), (U : Subgroup _) ≤ P →
      ∃ cuts : Set (Fin m), P = cutStabilizer b cuts) :
    ∃ i j : Fin m, i ≠ j ∧
      A ⊔ (U : Subgroup _) = minimalParabolic b i ∧
      B ⊔ (U : Subgroup _) = minimalParabolic b j ∧
      A = (pResidual 2 (minimalParabolic b i)).map (minimalParabolic b i).subtype ∧
      B = (pResidual 2 (minimalParabolic b j)).map (minimalParabolic b j).subtype ∧
      (A ⊔ B) ⊔ (U : Subgroup _) = cutStabilizer b ({i, j} : Set (Fin m))ᶜ := by
  have hia := CubicPairGeometry.cubic_join_index U A hna hca
  have hib := CubicPairGeometry.cubic_join_index U B hnb hcb
  obtain ⟨ca, hea⟩ := hcoords (A ⊔ U) le_sup_right
  obtain ⟨cb, heb⟩ := hcoords (B ⊔ U) le_sup_right
  have hia' : (cutStabilizer b Set.univ).relIndex (cutStabilizer b ca) = 3 := by
    rw [hea, hu] at hia
    exact hia
  have hib' : (cutStabilizer b Set.univ).relIndex (cutStabilizer b cb) = 3 := by
    rw [heb, hu] at hib
    exact hib
  obtain ⟨i, rfl⟩ := Linear.cuts_eq_compl_singleton_of_index_three b ca hia'
  obtain ⟨j, rfl⟩ := Linear.cuts_eq_compl_singleton_of_index_three b cb hib'
  have hne : i ≠ j := by
    intro he
    apply CubicPairGeometry.cubic_joins_ne U A B ha hb hna hnb hca hcab
    exact hea.trans (he ▸ heb.symm)
  change A ⊔ (U : Subgroup _) = minimalParabolic b i at hea
  change B ⊔ (U : Subgroup _) = minimalParabolic b j at heb
  refine ⟨i, j, hne, hea, heb, ?_, ?_, ?_⟩
  · rw [← hea]
    exact (embedded_pResidual_join_pGroup A U ha U.isPGroup' hna).symm
  · rw [← heb]
    exact (embedded_pResidual_join_pGroup B U hb U.isPGroup' hnb).symm
  · have hjoin : (A ⊔ B) ⊔ (U : Subgroup _) = (A ⊔ U) ⊔ (B ⊔ U) := by
      simp only [sup_left_comm, sup_comm, sup_idem]
    rw [hjoin, hea, heb]
    exact join_nodes b (fun P hP => hcoords P (hu.symm ▸ hP)) i j

private theorem pair_solvable_three_part {m : ℕ} (U : Sylow 2 (LinearGroup (m + 1)))
    (A B : Subgroup (LinearGroup (m + 1)))
    (hna : (U : Subgroup (LinearGroup (m + 1))) ≤ normalizer (A : Set (LinearGroup (m + 1))))
    (hnb : (U : Subgroup (LinearGroup (m + 1))) ≤ normalizer (B : Set (LinearGroup (m + 1))))
    (hcab : Nat.card ((A ⊔ B : Subgroup _) ⧸ pCore 2 (A ⊔ B : Subgroup _)) = 9) :
    Group.IsSolvable ((A ⊔ B) ⊔ (U : Subgroup _) : Subgroup _) ∧
      (Nat.card ((A ⊔ B) ⊔ (U : Subgroup _) : Subgroup _)).factorization 3 = 2 := by
  have hn : (U : Subgroup (LinearGroup (m + 1))) ≤
      normalizer ((A ⊔ B : Subgroup (LinearGroup (m + 1))) : Set (LinearGroup (m + 1))) :=
    (le_inf hna hnb).trans (normalizer_inf_normalizer_le_normalizer_sup A B)
  refine ⟨CubicPairGeometry.normalized_join_solvable (A ⊔ B) U U.isPGroup' hn 2 hcab, ?_⟩
  rw [CubicPairGeometry.normalized_join_three_part (A ⊔ B) U U.isPGroup' hn]
  exact CubicPairGeometry.three_part_of_core_quotient_nine (A ⊔ B) hcab

/-- Two normalized cubic residuals in binary four-space determine the two
ordered endpoints of one full Sylow flag. Every marking is retained. -/
theorem four_common_coordinates (U : Sylow 2 (LinearGroup 4))
    (A B : Subgroup (LinearGroup 4))
    (ha : IsPPerfect 2 A) (hb : IsPPerfect 2 B)
    (hna : (U : Subgroup (LinearGroup 4)) ≤ normalizer (A : Set _))
    (hnb : (U : Subgroup (LinearGroup 4)) ≤ normalizer (B : Set _))
    (hca : Nat.card (A ⧸ pCore 2 A) = 3) (hcb : Nat.card (B ⧸ pCore 2 B) = 3)
    (hcab : Nat.card ((A ⊔ B : Subgroup _) ⧸ pCore 2 (A ⊔ B : Subgroup _)) = 9) :
    ∃ (b : Basis 3) (i j : Fin 3),
      (U : Subgroup _) = cutStabilizer b Set.univ ∧
      A ⊔ (U : Subgroup _) = fourParabolic b {i} ∧
      B ⊔ (U : Subgroup _) = fourParabolic b {j} ∧
      A = fourNodeResidual b i ∧ B = fourNodeResidual b j ∧
      (A ⊔ B) ⊔ (U : Subgroup _) = fourParabolic b {i, j} ∧
      i ≠ j ∧ (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
      ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)) ∧
      (U : Subgroup _).relIndex (A ⊔ U) = 3 ∧
      (U : Subgroup _).relIndex (B ⊔ U) = 3 ∧
      Group.IsSolvable ((A ⊔ B) ⊔ (U : Subgroup _) : Subgroup _) ∧
      A ≠ B ∧ A ⊔ (U : Subgroup _) ≠ B ⊔ U := by
  obtain ⟨b, hu⟩ := sylow_eq_cutStabilizer U
  obtain ⟨i, j, hij, hea, heb, hra, hrb, heab⟩ :=
    marked_nodes U A B ha hb hna hnb hca hcb hcab b hu (four_overgroup_coordinates U b hu)
  obtain ⟨hs, _⟩ := pair_solvable_three_part U A B hna hnb hcab
  have hsf : Group.IsSolvable (cutStabilizer b ({i, j} : Set (Fin 3))ᶜ) := heab ▸ hs
  have hend := four_pair_endpoints b i j hij hsf
  have hn : i.val + 1 < j.val ∨ j.val + 1 < i.val := by
    rcases hend with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hne := CubicPairGeometry.cubic_joins_ne U A B ha hb hna hnb hca hcab
  refine ⟨b, i, j, hu, hea, heb, hra, hrb, heab, hij, hn, hend,
    CubicPairGeometry.cubic_join_index U A hna hca,
    CubicPairGeometry.cubic_join_index U B hnb hcb, hs, ?_, hne⟩
  exact fun h => hne (congrArg (fun E : Subgroup (LinearGroup 4) => E ⊔ U) h)

/-- The same intrinsic recognition in binary five-space, using precisely the
chapter's actual `fiveParabolic` and `fiveNodeResidual` subgroups. The first
node marks A and the second marks B; they are never reordered. -/
theorem five_common_coordinates (U : Sylow 2 (LinearGroup 5))
    (A B : Subgroup (LinearGroup 5))
    (ha : IsPPerfect 2 A) (hb : IsPPerfect 2 B)
    (hna : (U : Subgroup (LinearGroup 5)) ≤ normalizer (A : Set _))
    (hnb : (U : Subgroup (LinearGroup 5)) ≤ normalizer (B : Set _))
    (hca : Nat.card (A ⧸ pCore 2 A) = 3) (hcb : Nat.card (B ⧸ pCore 2 B) = 3)
    (hcab : Nat.card ((A ⊔ B : Subgroup _) ⧸ pCore 2 (A ⊔ B : Subgroup _)) = 9) :
    ∃ (b : FiveFlagGeometry.FiveBasis) (i j : Fin 4),
      (U : Subgroup _) = FiveFlagGeometry.flagStabilizer b Set.univ ∧
      A ⊔ (U : Subgroup _) = fiveParabolic b {i} ∧
      B ⊔ (U : Subgroup _) = fiveParabolic b {j} ∧
      A = fiveNodeResidual b i ∧ B = fiveNodeResidual b j ∧
      (A ⊔ B) ⊔ (U : Subgroup _) = fiveParabolic b {i, j} ∧
      i ≠ j ∧ (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
      (U : Subgroup _).relIndex (A ⊔ U) = 3 ∧
      (U : Subgroup _).relIndex (B ⊔ U) = 3 ∧
      Group.IsSolvable ((A ⊔ B) ⊔ (U : Subgroup _) : Subgroup _) ∧
      A ≠ B ∧ A ⊔ (U : Subgroup _) ≠ B ⊔ U := by
  obtain ⟨b, hu⟩ := sylow_eq_cutStabilizer U
  obtain ⟨i, j, hij, hea, heb, hra, hrb, heab⟩ :=
    marked_nodes U A B ha hb hna hnb hca hcb hcab b hu (five_overgroup_coordinates U b hu)
  obtain ⟨hs, h3⟩ := pair_solvable_three_part U A B hna hnb hcab
  have hsf : Group.IsSolvable (cutStabilizer b ({i, j} : Set (Fin 4))ᶜ) := heab ▸ hs
  have h3f : (Nat.card (cutStabilizer b ({i, j} : Set (Fin 4))ᶜ)).factorization 3 = 2 := heab ▸ h3
  have hn := five_pair_nonadjacent b i j hij hsf h3f
  have hne := CubicPairGeometry.cubic_joins_ne U A B ha hb hna hnb hca hcab
  refine ⟨b, i, j, hu, hea, heb, hra, hrb, heab, hij, hn,
    CubicPairGeometry.cubic_join_index U A hna hca,
    CubicPairGeometry.cubic_join_index U B hnb hcb, hs, ?_, hne⟩
  exact fun h => hne (congrArg (fun E : Subgroup (LinearGroup 5) => E ⊔ U) h)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.PairGeometry

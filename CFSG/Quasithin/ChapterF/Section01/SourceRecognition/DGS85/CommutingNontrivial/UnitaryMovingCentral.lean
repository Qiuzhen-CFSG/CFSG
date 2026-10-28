module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LinearMovingCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryCoreOmega
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CoreProductComparison
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.Suzuki.SmallOmegaResidual

/-!
# DGS 8.7 at a proper large-unitary edge core product

The moving unitary endpoint puts the neighboring core in the quotient Sylow
omega-center. The displacement commutator therefore centralizes the terminal
core, and the earlier critical-pair argument makes it centralize the terminal
two-residual. The terminal quotient is perfect: a linear terminal would force
the full edge product, while a small unitary, dihedral or Suzuki(2) terminal
contradicts the large-unitary lower bound on the common edge index. The residual
and core thus generate the terminal actor, placing the commutator in its center.

Source: DGS, *Groups and Graphs* (1985), 8.4 and 8.7, pp.137--140.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem terminal_unitary_quotient_perfect
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a' : Vertex (Reduction.reducedFamily L S₀)}
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily L S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)) 3 (2^n) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily L S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)) 3 (2^n))
    (hproper : ¬ (stabilizer (Reduction.reducedFamily L S₀) w.val ⊓
      stabilizer (Reduction.reducedFamily L S₀) a').pCoreIn 2 ≤
      Q (Reduction.reducedFamily L S₀) w.val ⊔ Q (Reduction.reducedFamily L S₀) a') :
    Group.IsPerfect (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite (d.localGroup a') := Finite.of_injective
    (inclusion (d.local_le a')) (inclusion_injective _)
  let : Finite (d.localGroup w.val) := Finite.of_injective
    (inclusion (d.local_le w.val)) (inclusion_injective _)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht
    (Reduction.reduced_borel_core_sylow h) d w.property.symm
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht
    (Reduction.reduced_borel_core_sylow h) d w.property
  have hidx : (2^n)^2 ≤ (Q Γ w.val ⊔ Q Γ a').relIndex
      ((stabilizer Γ w.val ⊓ stabilizer Γ a').pCoreIn 2) :=
    source_large_unitary_core_product_index_lower ht d w.property.symm
      (models w.val) R hR hn hu hproper
  have hpow : 4 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
  have hlarge : 16 ≤ (Q Γ a' ⊔ Q Γ w.val).relIndex
      ((stabilizer Γ a' ⊓ stabilizer Γ w.val).pCoreIn 2) := by
    have h16 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
    simpa only [sup_comm,inf_comm] using h16.trans hidx
  have hsmall_false (hs : (Q Γ a' ⊔ Q Γ w.val).relIndex
      ((stabilizer Γ a' ⊓ stabilizer Γ w.val).pCoreIn 2) ≤ 4) : False := by omega
  have hob : ¬ stabilizer Γ w.val ≤ normalizer
      ((Q Γ a' ⊓ Q Γ w.val : Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)) := by
    simpa only [inf_comm] using
      Reduction.reduced_graph_core_obstruction h w.val a' w.property.symm
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (d.localGroup a')))
  have hupper_of_card (hScard : Nat.card S ≤ 4) :
      (Q Γ a' ⊔ Q Γ w.val).relIndex
        ((stabilizer Γ a' ⊓ stabilizer Γ w.val).pCoreIn 2) ≤ 4 := by
    let L' := d.localGroup a'
    let q := QuotientGroup.mk' (pCore 2 L')
    let A := ((Q Γ w.val).subgroupOf L').map q
    have hQR : Q Γ w.val ≤ (T : Subgroup L').map L'.subtype := by
      rw [hT]
      have hQ := Noncommuting.graph_Q_le_edgeCore ht w.property.symm
      change Q Γ w.val ≤ (stabilizer Γ w.val ⊓ stabilizer Γ a').pCoreIn 2 at hQ
      change Q Γ w.val ≤ (stabilizer Γ a' ⊓ stabilizer Γ w.val).pCoreIn 2
      simpa only [inf_comm] using hQ
    have hQT : (Q Γ w.val).subgroupOf L' ≤ T := by
      intro x hx
      obtain ⟨y,hy,he⟩ := hQR hx
      exact (Subtype.ext he : y = x) ▸ hy
    have hAS : A ≤ S := map_mono hQT
    have hm := (A.subgroupOf S).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv] at hm
    change Nat.card A * A.relIndex S = Nat.card S at hm
    have hpos : 0 < Nat.card A := Nat.card_pos
    have hi : A.relIndex S ≤ 4 := by nlinarith
    have he := source_edge_core_product_index ht d w.property T hT
    change (Q Γ a' ⊔ Q Γ w.val).relIndex
      ((stabilizer Γ a' ⊓ stabilizer Γ w.val).pCoreIn 2) = A.relIndex S at he
    exact he ▸ hi
  cases models a' with
  | linear k hk hi =>
      exfalso
      have hfull := source_linear_edge_core_product ht d w.property
        (models a') T hT hob hk hi
      change Q Γ a' ⊔ Q Γ w.val =
        (stabilizer Γ a' ⊓ stabilizer Γ w.val).pCoreIn 2 at hfull
      apply hproper
      change (stabilizer Γ w.val ⊓ stabilizer Γ a').pCoreIn 2 ≤ Q Γ w.val ⊔ Q Γ a'
      simpa only [sup_comm,inf_comm] using hfull.ge
  | projective_unitary k hk hi =>
      by_cases hk2 : 2 ≤ k
      · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hi
        have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 k hk hK hconj
        have hpowk : 4 ≤ 2 ^ k := by
          simpa using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hk2
        let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
          J.projective_isPerfect_of_fixed_card (by omega) hK hfixed
        exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      · exfalso
        have hk1 : k = 1 := by omega
        apply hsmall_false
        exact source_small_unitary_core_product_index_le_four ht d w.property
          (models a') T hT hob (Or.inl (by
            change ClassicalGroup.IsPSU (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) 3 (2 ^ k) at hi
            simpa only [hk1,pow_one] using hi))
  | special_unitary k hk hi =>
      by_cases hk2 : 2 ≤ k
      · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hi
        have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 k hk hK hconj
        have hpowk : 4 ≤ 2 ^ k := by
          simpa using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hk2
        let : Group.IsPerfect J.specialSubgroup :=
          J.special_isPerfect_of_fixed_card (by omega) hK hfixed
        exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      · exfalso
        have hk1 : k = 1 := by omega
        apply hsmall_false
        exact source_small_unitary_core_product_index_le_four ht d w.property
          (models a') T hT hob (Or.inr (by
            change IsSU (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) 3 (2 ^ k) at hi
            simpa only [hk1,pow_one] using hi))
  | dihedral hi =>
      exfalso
      apply hsmall_false
      apply hupper_of_card
      have hc : Nat.card (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) = 10 := by
        obtain ⟨e⟩ := hi
        calc
          _ = Nat.card (DihedralGroup 5) := Nat.card_congr e.toEquiv
          _ = 10 := by rw [DihedralGroup.nat_card]
      rw [S.card_eq_multiplicity,hc]
      have hf : Nat.factorization 10 2 = 1 := by
        rw [show (10 : ℕ) = 2^1 * 5 by rfl, Nat.factorization_mul (by decide) (by decide),
          Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_five.factorization]
        norm_num
      rw [hf]
      norm_num
  | suzuki k hi =>
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · exfalso
        apply hsmall_false
        apply hupper_of_card
        have hc : Nat.card (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) =
            Nat.card (SuzukiMatrixGroup 0) := by
          obtain ⟨e⟩ := hi
          exact Nat.card_congr e.toEquiv
        rw [S.card_eq_multiplicity,hc,suzukiZero_card]
        have hf : Nat.factorization 20 2 = 2 := by
          rw [show (20 : ℕ) = 2^2 * 5 by rfl, Nat.factorization_mul (by decide) (by decide),
            Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_five.factorization]
          norm_num
        rw [hf]
        norm_num
      · obtain ⟨e⟩ := hi
        let : IsSimpleGroup (SuzukiMatrixGroup k) :=
          (BenderSuzuki.External.huppert_blackburn_XI_3_6 k hkpos).1
        let : Group.IsPerfect (SuzukiMatrixGroup k) := by
          constructor
          rcases (inferInstance : (commutator (SuzukiMatrixGroup k)).Normal).eq_bot_or_eq_top with hz | hz
          · exact False.elim (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable k hkpos
              ⟨⟨1,(derivedSeries_one _).trans hz⟩⟩)
          · exact hz
        exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem proper_unitary_perfect_terminal_central
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily L S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)) 3 (2^n) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily L S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)) 3 (2^n))
    (hproper : ¬ (stabilizer (Reduction.reducedFamily L S₀) w.val ⊓
      stabilizer (Reduction.reducedFamily L S₀) a').pCoreIn 2 ≤
      Q (Reduction.reducedFamily L S₀) w.val ⊔ Q (Reduction.reducedFamily L S₀) a')
    [Group.IsPerfect (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a'))] :
    let Γ := Reduction.reducedFamily L S₀
    ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≤ Z Γ a' := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let H := ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆
  let M := d.localGroup a'
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite M := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  let : Finite (d.localGroup w.val) := Finite.of_injective
    (inclusion (d.local_le w.val)) (inclusion_injective _)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d w.property.symm
  have hΩ := (source_critical_quotient_omega_action ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm R hR).1
  change H ≤ Z Γ w.val ⊓ centralizer (quotientSylowOmegaPreimage (d.localGroup w.val) R : Set (Reduction.G₀ L S₀)) at hΩ
  have hQ := source_unitary_neighbor_core_le_omega ht d w.property.symm
    (models w.val) R hR hn hu hproper
  have hHQ : H ≤ centralizer (Q Γ a' : Set (Reduction.G₀ L S₀)) :=
    (hΩ.trans inf_le_right).trans (centralizer_le hQ)
  have hescape : ¬ Q Γ w.val ≤ Q Γ a' := core_escape_of_intersection_obstruction Γ
    (Reduction.reduced_graph_core_obstruction h w.val a' w.property.symm)
  have hres := (source_critical_displacement_residual_fixed ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hescape).trans inf_le_right
  let : Group.IsPerfect (M ⧸ pCore 2 M) := by
    change Group.IsPerfect (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a'))
    infer_instance
  have hgen : pResidual 2 M ⊔ pCore 2 M = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 M)
    have hh : (pResidual 2 M).map q = ⊤ := by
      rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _),
        pResidual_eq_top_of_isPerfect]
    have hh' := congrArg (Subgroup.comap q) hh
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh'
  have hM : (pResidual 2 M).map M.subtype ⊔ Q Γ a' = M := by
    rw [←localGroup_core_eq Γ d a']
    change (pResidual 2 M).map M.subtype ⊔ (pCore 2 M).map M.subtype = M
    rw [←Subgroup.map_sup,hgen]
    exact (MonoidHom.range_eq_map M.subtype).symm.trans M.range_subtype
  have hHC : H ≤ centralizer (M : Set (Reduction.G₀ L S₀)) := by
    apply le_centralizer_iff.mp
    rw [←hM]
    exact sup_le (le_centralizer_iff.mp hres) (le_centralizer_iff.mp hHQ)
  have hHZ := hΩ.trans inf_le_left
  have hself : (graph Γ).dist a' a' + 1 ≤ b Γ := by
    simpa only [SimpleGraph.dist_self,zero_add] using hb.le
  have hHL : H ≤ M := (source_critical_displacement_residual_fixed ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hescape).trans
    (inf_le_left.trans (neighbor_le_graphLocalGroup ht (Reduction.reduced_kernel_sylow h) a' a' hb
      hself))
  have hz := critical_end_center_of_commuting Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (fun v => (source_Z_Q_U ht v).2) hc hcomm M (d.sylow_or_center a')
  change H ≤ Z Γ a'
  rw [hz]
  let : IsElementaryAbelian 2 (Z Γ w.val) := CommutingOneProfile.source_center_elementary ht w.val
  intro x hx
  exact (mem_omegaCenterIn_iff M x).mpr ⟨hHL hx,hHC hx,
    elemPow_eq_one_of_isElementaryAbelian x (hHZ hx)⟩


/-- DGS 8.7 for a moving unitary neighbor with parameter at least four and a
proper adjacent-core product. The retained terminal catalogue supplies all
perfectness needed by the residual-centralization argument. -/
theorem reduced_unitary_proper_moving_commutator_central
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily L S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)) 3 (2^n) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily L S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)) 3 (2^n))
    (hproper : ¬ (stabilizer (Reduction.reducedFamily L S₀) w.val ⊓
      stabilizer (Reduction.reducedFamily L S₀) a').pCoreIn 2 ≤
      Q (Reduction.reducedFamily L S₀) w.val ⊔ Q (Reduction.reducedFamily L S₀) a') :
    let Γ := Reduction.reducedFamily L S₀
    ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≤ Z Γ a' := by
  set_option linter.style.haveILetI false in
    letI := terminal_unitary_quotient_perfect h models w hn hu hproper
  exact proper_unitary_perfect_terminal_central h models hc hab hd hb hcomm w hm hn hu hproper

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

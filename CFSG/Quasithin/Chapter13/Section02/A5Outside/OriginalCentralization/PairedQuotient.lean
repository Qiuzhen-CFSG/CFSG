module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PairedBorel
public import Theory.GroupTheory.ResidualTwoByThreeJoin

/-!
# The paired outside case and the original Borel-join quotient

The original Borel residual L₁=O²(N_L(T∩L)) is identified with the
literal residual of C_L(V₁), not just with an isomorphic group. Its marked
A₄ action has two-group kernel, so L₁/O₂(L₁) has order three, and T
normalizes L₁. In the paired outside case, the proved normalization and
commutator calculation give [L₁,O²(H)]≤O₂(O²(H)). The normal-core join
lemma therefore makes O²(H₀/O₂(H₀)) a three-group for H₀=⟨H,L₁⟩.
Passing to O₃′(H₀) gives exactly the quotient contradicted in 13.2.13.
Consequently only the single-factor S₃/C₃ models survive when that earlier
exclusion is available.

The independent Baumann bound, solvability, faithful-component normalization,
and source 13.2.12--13 remain explicit. This proves the paired quotient step
of 13.2.14 and its conditional single-factor conclusion; it does not assert
unconditional 13.2.7. Their remaining local discharge stays with
qt-d-1367-assembly, and the 13.3.2 source input retains its existing owner.

Source: Aschbacher--Smith 13.2.8--14, printed pp.880--883.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.TerminalContradiction.Ratio
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The two literal inclusions in the original Borel residual agree with
the embedded residual of the original line centralizer. -/
theorem borelResidual_eq_point_residual :
    borelResidual T L = residualCentralizer L V₁ := by
  let N := normalizer ((T : Subgroup G).subgroupOf L : Set L)
  have hN : N.map L.subtype = ChapterF.Source.borel L (T : Subgroup G) := by
    change (normalizer ((T : Subgroup G).subgroupOf L : Set L)).map L.subtype =
      L ⊓ normalizer ((T : Subgroup G) ⊓ L : Set G)
    rw [← inf_subgroupOf_right (T : Subgroup G) L,
      ← subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ L ≤ L from inf_le_right),
      subgroupOf_map_subtype,inf_comm]
    rfl
  change ((pResidual 2 N).map N.subtype).map L.subtype = _
  rw [map_embedded_pResidual,hN,d.borel_eq_point_centralizer]
  rfl

/-- The prescribed Sylow normalizes the original Borel residual. -/
theorem sylow_normalizes_borelResidual :
    (T : Subgroup G) ≤ normalizer (borelResidual T L : Set G) := by
  rw [borelResidual_eq_point_residual d]
  exact (le_normalizer_inf d.normalizes_L
    (d.flag.one_invariant.trans (normalizer_le_normalizer_centralizer V₁))).trans
      (normalizer_le_normalizer_characteristic_image (L ⊓ centralizer (V₁ : Set G))
        (pResidual 2 (L ⊓ centralizer (V₁ : Set G) : Subgroup G)))

/-- The genuine original Borel residual modulo its own two-core has order three. -/
theorem borelResidual_quotient_card :
    Nat.card (borelResidual T L ⧸ pCore 2 (borelResidual T L)) = 3 := by
  rw [borelResidual_eq_point_residual d]
  obtain ⟨g,hz,_,_,_,_⟩ := d.flag.exists_coordinate_witness
  let f := d.flag.relabel g
  have hline : (zpowers (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.z)).map
      f.module.map = V₁ := by
    have hh := congrArg (Subgroup.map d.flag.module.map) hz
    rw [MonoidHom.map_zpowers,d.flag.preimage_map V₁
      (d.flag.one_le_two.trans d.flag.two_le_V)] at hh
    rw [MonoidHom.map_zpowers]
    exact hh
  let q := Section05.A5Source.ThirdSpace.residualAction f.module hline
  have hk : q.ker = f.module.action.ker.comap
      (inclusion (show residualCentralizer L V₁ ≤ L from
        Section05.A5Source.ThirdSpace.residual_le_centralizer.trans inf_le_left)) := by
    ext x
    exact Subtype.ext_iff
  have htwo : IsPGroup 2 q.ker := by
    rw [hk,f.action_kernel]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  let e := q.pCoreQuotientEquiv
    (Section05.A5Source.ThirdSpace.residualAction_surjective f.module hline) htwo
  rw [Nat.card_congr e.toEquiv,←BinaryPermutation.AlternatingFiveBorel.sectionKernel_eq_twoCore]
  exact BinaryPermutation.AlternatingFiveBorel.card_quotient_actor

/-- In the paired outside case the literal Borel join has three-group
two-residual after quotienting by its two-core. -/
theorem paired_borel_join_residual_mod_twoCore_isThree
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hpair : Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 ≠ ⊥) :
    let J := H ⊔ borelResidual T L
    IsPGroup 3 (pResidual 2 (J ⧸ pCore 2 J)) := by
  let A := borelResidual T L
  let R := (pResidual 2 H).map H.subtype
  let J := H ⊔ A
  have hAJ : A ≤ J := le_sup_right
  have hRJ : R ≤ J := (map_subtype_le _).trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := hH.1.1.2.trans (show H ≤ J from le_sup_left)
  have hAR : A ≤ normalizer (R : Set G) :=
    paired_borelResidual_normalizes_residual_of_join_core d hn hH hB hZ hs hpair hcore
  have hJR : J ≤ normalizer (R : Set G) :=
    sup_le (le_normalizer_embedded_pResidual 2 H) hAR
  let : (R.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJR
  have hRA : IsPGroup 3 (A ⧸ pCore 2 A) :=
    IsPGroup.of_card (n := 1) (borelResidual_quotient_card d)
  have hRR : IsPGroup 3 (R ⧸ pCore 2 R) := by
    let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    let := source_residual_core_quotient_elementary d hH hB hZ hs
    exact (IsElementaryAbelian.isPGroup 3 _).of_equiv eQ
  have transport (K : Subgroup G) (hKJ : K ≤ J)
      (hK : IsPGroup 3 (K ⧸ pCore 2 K)) :
      IsPGroup 3 (K.subgroupOf J ⧸ pCore 2 (K.subgroupOf J)) := by
    let e := subgroupOfEquivOfLe hKJ
    exact hK.of_equiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  apply twoResidual_mod_twoCore_isThree_of_normalized_join
    (A.subgroupOf J) (R.subgroupOf J) ((T : Subgroup G).subgroupOf J)
    (transport A hAJ hRA) (transport R hRJ hRR) T.isPGroup'.comap_subtype
  · intro t ht
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (sylow_normalizes_borelResidual d ht) (a : G)
  · apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hRJ,
      map_subgroupOf_eq_of_le hAJ,map_subgroupOf_eq_of_le hTJ,
      ←MonoidHom.range_eq_map,range_subtype]
    have hg := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hg
    change R ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = H at hg
    rw [map_subgroupOf_eq_of_le hH.1.1.2] at hg
    calc
      R ⊔ A ⊔ (T : Subgroup G) = (R ⊔ (T : Subgroup G)) ⊔ A := by ac_rfl
      _ = J := by rw [hg]
  · apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_commutator,map_pCoreIn_of_injective 2 _ J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hAJ,map_subgroupOf_eq_of_le hRJ]
    exact (paired_borel_join_control d hn hH hB hZ hs hpair hcore).2.2

/-- The precise quotient used in the final contradiction of 13.2.14. -/
theorem paired_borel_join_residual_mod_primeToThreeCore_isThree
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hpair : Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 ≠ ⊥) :
    let J := H ⊔ borelResidual T L
    IsPGroup 3 (pResidual 2 (J ⧸ pPrimeCore 3 J)) :=
  twoResidual_mod_primeToThreeCore_isThree
    (paired_borel_join_residual_mod_twoCore_isThree d hn hH hB hZ hs hpair hcore)

/-- Original 13.2.14 from the earlier source 13.2.12--13 inputs, with both
literal source quotient models of the surviving single-factor case. -/
theorem single_quotients_of_non_three_borel_join
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 ≠ ⊥)
    (hnot : let J := H ⊔ borelResidual T L
      ¬ IsPGroup 3 (pResidual 2 (J ⧸ pPrimeCore 3 J))) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∧
      Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Multiplicative (ZMod 3)) := by
  rcases source_residual_core_quotient_models d hH hB hZ hs with h | h
  · exact h
  · exact (hnot (paired_borel_join_residual_mod_primeToThreeCore_isThree
      d hn hH hB hZ hs h.1 hcore)).elim

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

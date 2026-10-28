module
public import Stellmacher.SectionEight.LemmaEightOneOffender
public import Stellmacher.SectionEight.LocalQuotientHypotheses
public import Stellmacher.SectionThree.NormalClosureResidualJoin
public import Stellmacher.SectionOne.OneSevenIdentification

/-!
# The decomposition group in Stellmacher (8.1)

For the initial center's exact quotient-module witness, the normal closure
of its offender-generated J is the join of J with the projected local
2-residual. This identifies the group to which the factor/module product
of (1.7) is applied in (8.1)(b), Journal of Algebra 190 (1997), p.37.

Critical minimality puts the final center in the distinguished Sylow
subgroup. The proved offender lemma puts its image in J. The global
identification from (1.7) makes J normal in that Sylow image, while reversed
criticality prevents its lift from lying in the local 2-core. The general
Section 3 normal-closure/residual theorem then gives the equality. All
constructions retain the witness's named action and actual projection.
The graph-local theorem is owned at this layer so opposite-closure proofs
can use it independently of the later center-order-four argument. Its
canonical counterpart is a graph-preserving wrapper.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- The action-defined normal closure is the projected local residual joined with J. -/
public theorem lemma_eight_one_residual_join_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    SectionOne.oneE (G := w.X) (V := ZAt ctx.Γ ctx.criticalPath.a)
      ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) =
    ((EAt ctx.Γ ctx.criticalPath.a).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.a)).map w.projection ⊔
    SectionOne.oneJ (G := w.X) (V := ZAt ctx.Γ ctx.criticalPath.a)
      ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) := by
  classical
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Sb := (S.subgroupOf P).map w.projection
  let J := SectionOne.oneJ (V := z Γ cp.a) Sb
  have h74 := lemma_seven_four h Γ cp
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hlen := cp.length_pos
  let last : Γ.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hlastadj : Γ.adjacent cp.a' last := by
    have he := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hi, cp.path_end] at he
    exact Γ.adjacent_symm he
  have hlast := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hlast
  have hZendS : z Γ cp.a' ≤ S := by
    have hdist : Γ.distance cp.a' cp.firstStep < cp.length := by
      rw [Γ.distance_symm]
      have hd := SevenSix.path_distance_le Γ cp 1 cp.length (by omega) le_rfl
      have hd' : Γ.distance cp.firstStep cp.a' ≤ cp.length - 1 := by
        simpa [cp.path_first, cp.path_end] using hd
      omega
    exact (SevenSix.critical_minimality Γ cp hdist).trans
      (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hSP : S ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hnotcentral : ¬ z Γ cp.a' ≤ Subgroup.centralizer (z Γ cp.a : Set G) := by
    intro hc
    apply ctx.commutator_ne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc
  have hlocal := local_quotient_hypotheses h Γ cp.a hfirst w (z Γ cp.a')
    (hZendS.trans hSP) hnotcentral
  have hP := (SevenSix.edge_local_data h Γ cp).1
  obtain ⟨_, U, hU⟩ := hP.1.1.2.1
  have hUSP : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUSP]
  have hid := (SectionOne.oneSeven_global_identification hlocal Ub).1
  rw [hUb] at hid
  have hJN := (SectionOne.oneSeven_global_product hlocal Ub).1
  let : (SectionOne.oneSevenGenerated (G := w.X) (V := z Γ cp.a)).Normal := hJN
  have hJS : J ≤ Sb := by
    change SectionOne.oneJ (V := z Γ cp.a) Sb ≤ Sb
    rw [hid]
    exact inf_le_left
  have hJn : (J.subgroupOf Sb).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hJS).mpr
    apply Subgroup.le_normalizer_iff.mpr
    intro s hs j hj
    change j ∈ SectionOne.oneJ (V := z Γ cp.a) Sb at hj
    change s * j * s⁻¹ ∈ SectionOne.oneJ (V := z Γ cp.a) Sb
    rw [hid] at hj ⊢
    exact ⟨Sb.mul_mem (Sb.mul_mem hs hj.1) (Sb.inv_mem hs),
      hJN.conj_mem j hj.2 s⟩
  have hZendJ : ((z Γ cp.a').subgroupOf P).map w.projection ≤ J :=
    le_sSup (eight_five_offender_local ctx w).1
  have hnot : ¬ S ⊓ (J.comap w.projection).map P.subtype ≤ twoCoreAmbient P := by
    intro hT
    apply (h74.commutator_case ctx.commutator_ne).2.2
    intro y hy
    have hyT : y ∈ S ⊓ (J.comap w.projection).map P.subtype := by
      refine ⟨hZendS hy, ?_⟩
      let yP : P := ⟨y, hZendS.trans hSP hy⟩
      exact Subgroup.mem_map.mpr ⟨yP,
        hZendJ (Subgroup.mem_map_of_mem w.projection hy), rfl⟩
    have hyQ := hT hyT
    rw [Γ.twoCoreAt_def]
    exact hyQ
  have hres := SectionThree.normalClosure_eq_residual_sup_of_normal_sylow_image
    S (SevenSix.sectionThreeHypotheses h) P
    ((pFamily_iff_pSet (⊤ : Subgroup G) S P).mp hP.1) hP.2
    w.projection w.surjective J hJS hJn hnot
  change Subgroup.normalClosure (J : Set w.X) =
    ((Γ.e cp.a).subgroupOf P).map w.projection ⊔ J
  have hEa : Γ.e cp.a = twoResidualAmbient P := Γ.twoResidualAt_def cp.a
  rw [hEa]
  exact hres


/-- The action-defined normal closure is the projected local residual joined with J. -/
public theorem lemma_eight_one_residual_join
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    SectionOne.oneE (G := w.X) (V := ZAt ctx.Γ ctx.criticalPath.a)
      ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) =
    ((EAt ctx.Γ ctx.criticalPath.a).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.a)).map w.projection ⊔
    SectionOne.oneJ (G := w.X) (V := ZAt ctx.Γ ctx.criticalPath.a)
      ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) := by
  exact lemma_eight_one_residual_join_local ctx.toLocalContext w

end Stellmacher.SectionEight

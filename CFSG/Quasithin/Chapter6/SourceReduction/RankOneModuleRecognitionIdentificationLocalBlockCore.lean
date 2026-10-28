module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalBlockAction
public import CFSG.Quasithin.Chapter6.Section01.QuotientA5
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoGeneration
public import Theory.GroupTheory.Commutator.ResidualNormalGeneration

/-!
# The original closure and the local block layer

The closure U is not contained in O₂(LT), since its fixed subgroup on V
has order four while U has order sixteen. Normal generation in the actual
quasisimple quotient of L therefore gives L=[L,U]. Three-subgroup commutation
identifies [O₂(LT),L] with V. These displacements are central of exponent two,
so every square in the local core centralizes L. The earlier conclusion
C_T(L)=1 makes that core elementary abelian.

Source: Aschbacher--Smith, 6.2.11, printed p.686, the block paragraph.
The equality V=O₂(LT) and the ambient A₇ contradiction remain outstanding.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G] [Finite G]

private theorem component_le_normal_closure (K T U : Subgroup G) [K.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hp : IsPPerfect 2 K) (hT : IsPGroup 2 T) (hgen : K ⊔ T = ⊤)
    (hU : IsPGroup 2 U) (hne : ¬ U ≤ pCore 2 G) :
    K ≤ normalClosure (U : Set G) := by
  let N := normalClosure (U : Set G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let D := N.map q
  have hq := QuotientGroup.mk'_surjective (pCore 2 G)
  let : B.Normal := Normal.map inferInstance q hq
  let : D.Normal := Normal.map inferInstance q hq
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hquot : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (T.map q) (hT.map q) (by
      rw [← Subgroup.map_sup, hgen, map_top_of_surjective q hq])
  obtain ⟨u, hu, huQ⟩ := Set.not_subset.mp hne
  have hBD : B ≤ D := quasisimple_le_normal_of_two_escape B D (U.map q)
    hquot (pCore_quotient_pCore_eq_bot 2) (hU.map q) (q u)
    (mem_map_of_mem q hu) (mem_map_of_mem q (le_normalClosure hu))
    (fun he => huQ ((QuotientGroup.eq_one_iff u).mp he))
  apply le_normal_of_isPPerfect_of_le_sup_pGroup K N (pCore 2 G) hp pCore_isPGroup
  have hh := map_le_iff_le_comap.mp hBD
  simpa only [D, comap_map_eq, q, QuotientGroup.ker_mk'] using hh

omit [Finite G] in
private theorem commutator_le_of_generated_actor (K U Q V : Subgroup G)
    [Q.Normal] [V.Normal] (hK : K = ⁅K, U⁆) (hQU : ⁅Q, U⁆ ≤ V) :
    ⁅Q, K⁆ ≤ V := by
  let q := QuotientGroup.mk' V
  have hzero : (⁅⁅K, U⁆, Q⁆).map q = ⊥ := by
    rw [map_commutator, map_commutator]
    apply commutator_commutator_eq_bot_of_rotate
    · rw [← map_commutator, ← map_commutator]
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
      exact (commutator_mono (by rwa [commutator_comm] : ⁅U, Q⁆ ≤ V) le_rfl).trans
        (commutator_le_left V K)
    · rw [← map_commutator, ← map_commutator]
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
      exact (commutator_mono (commutator_le_left Q K) le_rfl).trans hQU
  rw [← hK, commutator_comm] at hzero
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hzero

variable {P : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

private theorem local_component_quotient_quasisimple
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n) :
    IsQuasisimple ((L.subgroupOf (L ⊔ (P : Subgroup G))) ⧸
      pCore 2 (L.subgroupOf (L ⊔ (P : Subgroup G)))) := by
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  obtain ⟨e⟩ := h.quotient_a5_of_n_eq_two hnatural.1
  let c := subgroupOfEquivOfLe (show L ≤ L ⊔ (P : Subgroup G) from le_sup_left)
  exact IsQuasisimple.of_mulEquiv
    ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e).symm

/-- The original closure generates the entire component by commutators.
Normal generation uses its nontrivial action on V and the actual
quasisimple quotient of L inside LT. -/
theorem four_component_commutator_closure
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    L = ⁅L, sourceClosure (P : Subgroup G) L R z⁆ := by
  let X := L ⊔ (P : Subgroup G)
  let U := sourceClosure (P : Subgroup G) L R z
  let K := L.subgroupOf X
  let T := (P : Subgroup G).subgroupOf X
  let A := U.subgroupOf X
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes_L)
  let : IsQuasisimple (K ⧸ pCore 2 K) := local_component_quotient_quasisimple h hnatural
  have hK : K.IsCComponent := h.local_mem.1.prop.1
  let := hK.perfect
  have hKT : K ⊔ T = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ X from le_sup_left)
      (show (P : Subgroup G) ≤ X from le_sup_right)]
    exact subgroupOf_self _
  have hUT : U ≤ (P : Subgroup G) := by
    have hc := pCoreIn_le_sylow (Centralizer z) (P.subtype hP)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hP] at hc
    exact (local_closure_core h hnatural hz ho hP).1.trans hc
  have hUX : U ≤ X := hUT.trans le_sup_right
  have hnot : ¬ U ≤ X.pCoreIn 2 := by
    intro hUQ
    have he : U = ZS (P : Subgroup G) L R :=
      (inf_eq_left.mpr (hUQ.trans (local_core_centralizes_layer h))).symm.trans
        (four_closure_centralizer_layer h hnatural hz ho hP hplane hcard)
    have hc := four_closure_card h hnatural hz ho hP hplane hcard
    change Nat.card U = 16 at hc
    rw [he, (h.natural_ZS_geometry hnatural).2.1] at hc
    contradiction
  have hne : ¬ A ≤ pCore 2 X := by
    intro hh
    apply hnot
    have hm := map_mono (f := X.subtype) hh
    rwa [map_subgroupOf_eq_of_le hUX] at hm
  have hp : IsPPerfect 2 K := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hn
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
    let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  have hAN : T ≤ normalizer (A : Set X) := by
    rw [← subgroupOf_normalizer_eq hUX]
    exact comap_mono (hP.trans (closure_normalized _ _ _ _))
  have hgen := component_le_normal_closure K T A hK hp P.isPGroup'.comap_subtype hKT
    (P.isPGroup'.to_le hUT).comap_subtype hne
  have hh := eq_commutator_of_normalClosure_contains K T A hKT hp
    (P.isPGroup'.to_le hUT).comap_subtype hAN hgen
  have hm := congrArg (Subgroup.map X.subtype) hh
  rwa [map_commutator, map_subgroupOf_eq_of_le (show L ≤ X from le_sup_left),
    map_subgroupOf_eq_of_le hUX] at hm

/-- The local two-core has exactly V as its L-commutator. This is the
block layer identity in 6.2.11, with no LocalAnalysis assumption. -/
theorem four_local_core_commutator_component
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    ⁅(L ⊔ (P : Subgroup G)).pCoreIn 2, L⁆ = layer L R := by
  let X := L ⊔ (P : Subgroup G)
  let K := L.subgroupOf X
  let U := sourceClosure (P : Subgroup G) L R z
  let A := U.subgroupOf X
  let B := (layer L R).subgroupOf X
  have hUX : U ≤ X := by
    have hc := pCoreIn_le_sylow (Centralizer z) (P.subtype hP)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hP] at hc
    exact ((local_closure_core h hnatural hz ho hP).1.trans hc).trans le_sup_right
  have hBX : layer L R ≤ X := h.layer_le_L.trans le_sup_left
  have hXB : X ≤ normalizer (layer L R : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnatural.2.1
    exact sup_le hm.normalizes h.sylow_normalizes_layer
  let : B.Normal := normal_subgroupOf_of_le_normalizer hXB
  have hK : K = ⁅K, A⁆ := by
    apply map_injective X.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (show L ≤ X from le_sup_left),
      map_subgroupOf_eq_of_le hUX]
    exact four_component_commutator_closure h hnatural hz ho hP hplane hcard
  have hQA : ⁅pCore 2 X, A⁆ ≤ B := by
    intro x hx
    have hm := mem_map_of_mem X.subtype hx
    rw [map_commutator, map_subgroupOf_eq_of_le hUX, commutator_comm] at hm
    exact (show ZS (P : Subgroup G) L R ≤ layer L R from inf_le_left)
      (four_closure_local_core_commutator h hnatural hz ho hP hplane hcard hm)
  have hh := commutator_le_of_generated_actor K A (pCore 2 X) B hK hQA
  have hm := map_mono (f := X.subtype) hh
  rw [map_commutator, map_subgroupOf_eq_of_le (show L ≤ X from le_sup_left),
    map_subgroupOf_eq_of_le hBX] at hm
  exact le_antisymm hm (commutator_mono (reduced_le_core h.V_mem) le_rfl)

/-- Every square in the original local core centralizes L, since its
L-displacements lie in the central elementary layer. The source hypothesis
C_T(L)=1 therefore makes the core elementary abelian. -/
theorem four_local_core_elementary
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    IsElementaryAbelian 2 ((L ⊔ (P : Subgroup G)).pCoreIn 2) := by
  let Q := (L ⊔ (P : Subgroup G)).pCoreIn 2
  let := h.layer_elementary
  have hQT : Q ≤ (P : Subgroup G) := by
    change (L ⊔ (P : Subgroup G)).pCoreIn 2 ≤ (P : Subgroup G)
    rw [← sylow_layer_centralizer_eq_core h (hnatural.1 ▸ hnatural.2.1)]
    exact inf_le_left
  have hdisp := four_local_core_commutator_component h hnatural hz ho hP hplane hcard
  have hpow (q : Q) : q ^ 2 = 1 := by
    have hc : (q : G) ^ 2 ∈ centralizer (L : Set G) := by
      apply mem_centralizer_iff.mpr
      intro l hl
      let c := ⁅l, (q : G)⁆
      have hcV : c ∈ layer L R := by
        rw [← hdisp, commutator_comm]
        exact commutator_mem_commutator hl q.property
      have hc2 : c ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian c hcV
      have hcomm : Commute c (q : G) :=
        mem_centralizer_iff.mp (local_core_centralizes_layer h q.property) c hcV
      have he : l * (q : G) ^ 2 * l⁻¹ = (q : G) ^ 2 := by
        calc
          _ = (l * (q : G) * l⁻¹) ^ 2 := by simp [pow_two, mul_assoc]
          _ = (c * (q : G)) ^ 2 := by
            congr 1
            dsimp [c]
            group
          _ = c ^ 2 * (q : G) ^ 2 := hcomm.mul_pow 2
          _ = (q : G) ^ 2 := by rw [hc2, one_mul]
      exact mul_inv_eq_iff_eq_mul.mp he
    apply Subtype.ext
    exact show (q : G) ^ 2 ∈ (⊥ : Subgroup G) from
      hnatural.2.2.1 ▸ ⟨(P : Subgroup G).pow_mem (hQT q.property) 2, hc⟩
  have hi (q : Q) : q⁻¹ = q := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hpow q)
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  intro a b
  have hh := mul_inv_rev a b
  simpa only [hi] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction

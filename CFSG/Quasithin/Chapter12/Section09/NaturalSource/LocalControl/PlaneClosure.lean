module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Stages
public import CFSG.Quasithin.Chapter12.Section08.Setup.Completion
public import Theory.GroupTheory.PrimeRankNormalPair
public import Theory.GroupTheory.SymmetricThreeTwoCoreGeneration
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The new plane normal closure in 12.9.6

Let R=O₂(G₁). The full action of the original omitted-point parabolic P₂ on
V₂ shows that ⟨R^G₂⟩=⟨R^P₂⟩≤P₂. If R moves V₂, its nontrivial two-group
image normally generates S₃. Thus the literal I₂=⟨R^G₂⟩ has quotient S₃,
its two-core is C_I₂(V₂), and I₂T=P₂ has index three over T.

I₂ and C_G(V₂) normalize one another and intersect in a two-group. Their
three-ranks therefore add, and quasithinness gives m₃(C_G(V₂))≤1. Relative
normality of the actual K₁ transfers the premise [V₂,O₂(K₁)]≠1 to R.
This proves 12.9.6(2–3) from (1), which remains with the same source owner,
qt-d-1291-natural-source. It does not assert the missing movement premise.
The new I₂ is deliberately separate from the earlier U-span of 12.8.

Source: Aschbacher--Smith, 12.9.6, printed pp.861–862 of refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The new I₂ of 12.9.6, distinct from the U-span in 12.8. -/
def planeCoreClosure (F : InvariantFlag T V n) : Subgroup G :=
  conjugateSpanBy (F.H.pCoreIn 2) (F.Gi 2)

omit [Finite G] in
private theorem core_le_sylow {H : Subgroup G} (ht : (T : Subgroup G) ≤ H) :
    H.pCoreIn 2 ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le ht] using
    pCoreIn_le_sylow H (T.subtype ht)

omit [Finite G] in
private theorem sylow_le_parabolic (F : InvariantFlag T V n) :
    (T : Subgroup G) ≤ F.P L := by
  intro t ht
  exact ⟨mem_sup_right ht, mem_iInf.mpr fun i => mem_iInf.mpr fun _ => F.invariant i ht⟩

omit [Finite G] in
private theorem plane_centralizer_le_point (F : InvariantFlag T V n) :
    centralizer (F.Vi 2 : Set G) ≤ F.H :=
  (centralizer_le (F.monotone (by omega))).trans (Subgroup.centralizer_le_normalizer _)

/-- The full P-action removes the plane-centralizer factor from the core span. -/
theorem planeCoreClosure_eq_parabolic_span
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n) :
    planeCoreClosure F = conjugateSpanBy (F.H.pCoreIn 2) (F.P L) := by
  let := h.chosen.elementary
  apply conjugateSpanBy_eq_of_action_image (F.Vi 2)
  · exact F.P_le_G₂ (by have := h.rank; omega) L h.chosen.normalizes
  · exact (plane_centralizer_le_point F).trans
      (F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
  · exact F.binaryPlaneAction_image (by have := h.rank; omega) L h.chosen.normalizes
      (h.binarySeedAction_surjective F)

/-- The original point core has its G₂-normal closure inside the original P. -/
theorem planeCoreClosure_le_parabolic
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n) :
    planeCoreClosure F ≤ F.P L := by
  rw [planeCoreClosure_eq_parabolic_span h F]
  exact conjugateSpanBy_le_self ((core_le_sylow (F.invariant 1)).trans (sylow_le_parabolic F))

/-- Relative normality is in G₂, not in the ambient simple group. -/
theorem planeCoreClosure_normal
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n) :
    ((planeCoreClosure F).subgroupOf (F.Gi 2)).Normal := by
  exact (normal_subgroupOf_iff_le_normalizer
    ((planeCoreClosure_le_parabolic h F).trans
      (F.P_le_G₂ (by have := h.rank; omega) L h.chosen.normalizes))).mpr
        (le_normalizer_conjugateSpanBy _ _)

/-- The full plane action identifies the quotient of the actual omitted-point parabolic. -/
theorem parabolic_plane_quotient
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) :
    (F.P L).pCoreIn 2 = F.P L ⊓ centralizer (F.Vi 2 : Set G) ∧
      Nonempty (((F.P L) ⧸ pCore 2 (F.P L)) ≃* Equiv.Perm (Fin 3)) := by
  let := h.chosen.elementary
  let hn : 2 ≤ n := by have := h.rank; omega
  let f := F.binaryPermutationAction hn L h.chosen.normalizes
  have hf : Function.Surjective f := F.binaryPermutationAction_surjective hn L
    h.chosen.normalizes (h.binarySeedAction_surjective F)
  have hk : f.ker = pCore 2 (F.P L) :=
    (F.binaryPermutationAction_ker hn L h.chosen.normalizes).trans
      (F.binaryPlaneAction_ker_eq_twoCore hn L h.chosen.normalizes
        (h.binarySeedAction_surjective F) (h.centralizer_LT earlier.structural))
  exact ⟨(F.binary_parabolic_core hn L h.chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT earlier.structural)).1.symm,
    ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩⟩

/-- Nontrivial point-core action normally generates P modulo its two-core. -/
theorem planeCoreClosure_sup_parabolic_core
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hm : ⁅F.Vi 2, F.H.pCoreIn 2⁆ ≠ ⊥) :
    planeCoreClosure F ⊔ (F.P L).pCoreIn 2 = F.P L := by
  obtain ⟨hk, ⟨e⟩⟩ := parabolic_plane_quotient h earlier F
  have hRP : F.H.pCoreIn 2 ≤ F.P L :=
    (core_le_sylow (F.invariant 1)).trans (sylow_le_parabolic F)
  have hout : ¬ F.H.pCoreIn 2 ≤ (F.P L).pCoreIn 2 := by
    intro hc
    apply hm
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hc.trans (hk.le.trans inf_le_right))
  rw [planeCoreClosure_eq_parabolic_span h F]
  exact (Subgroup.core_hyperplane_and_generation (F.P L) (F.H.pCoreIn 2) hRP
    (isPGroup_pCoreIn 2 F.H) hout e).2

/-- The source's literal identity I₂T=P₂. -/
theorem planeCoreClosure_sup_sylow
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hm : ⁅F.Vi 2, F.H.pCoreIn 2⁆ ≠ ⊥) :
    planeCoreClosure F ⊔ (T : Subgroup G) = F.P L := by
  apply le_antisymm (sup_le (planeCoreClosure_le_parabolic h F) (sylow_le_parabolic F))
  rw [← planeCoreClosure_sup_parabolic_core h earlier F hm]
  exact sup_le_sup_left (core_le_sylow (sylow_le_parabolic F)) _

/-- The literal plane action of I₂ is full; no model marking is assumed. -/
theorem planeCoreClosure_action_surjective
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hm : ⁅F.Vi 2, F.H.pCoreIn 2⁆ ≠ ⊥) :
    Function.Surjective (setupSeedAction (planeCoreClosure F) (F.Vi 2)
      ((planeCoreClosure_le_parabolic h F).trans
        (F.P_le_G₂ (by have := h.rank; omega) L h.chosen.normalizes))) := by
  let := h.chosen.elementary
  let hn : 2 ≤ n := by have := h.rank; omega
  let f := F.binaryPlaneAction hn L h.chosen.normalizes
  have hk : f.ker = pCore 2 (F.P L) := F.binaryPlaneAction_ker_eq_twoCore hn L
    h.chosen.normalizes (h.binarySeedAction_surjective F) (h.centralizer_LT earlier.structural)
  let I := (planeCoreClosure F).subgroupOf (F.P L)
  have hgen : I ⊔ pCore 2 (F.P L) = ⊤ := by
    apply map_injective (F.P L).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (planeCoreClosure_le_parabolic h F)]
    change planeCoreClosure F ⊔ (F.P L).pCoreIn 2 = (⊤ : Subgroup (F.P L)).map (F.P L).subtype
    rw [planeCoreClosure_sup_parabolic_core h earlier F hm, ← MonoidHom.range_eq_map, range_subtype]
  have himage : I.map f = ⊤ := by
    have he := congrArg (map f) hgen
    have hzero : f.ker.map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
    rw [Subgroup.map_sup, ← hk, hzero, sup_bot_eq,
      map_top_of_surjective _ (F.binaryPlaneAction_surjective hn L h.chosen.normalizes
        (h.binarySeedAction_surjective F))] at he
    exact he
  intro a
  obtain ⟨i, hi, he⟩ := (show a ∈ I.map f by rw [himage]; trivial)
  exact ⟨⟨i, hi⟩, he⟩

/-- Both quotient and kernel assertions of 12.9.6(2), on the original I₂. -/
theorem planeCoreClosure_quotient
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hm : ⁅F.Vi 2, F.H.pCoreIn 2⁆ ≠ ⊥) :
    (planeCoreClosure F).pCoreIn 2 = planeCoreClosure F ⊓ centralizer (F.Vi 2 : Set G) ∧
      Nonempty (((planeCoreClosure F) ⧸ pCore 2 (planeCoreClosure F)) ≃* Equiv.Perm (Fin 3)) := by
  let := h.chosen.elementary
  let hn : 2 ≤ n := by have := h.rank; omega
  let f := setupSeedAction (planeCoreClosure F) (F.Vi 2)
    ((planeCoreClosure_le_parabolic h F).trans (F.P_le_G₂ hn L h.chosen.normalizes))
  let e := F.binaryPlaneLabel hn
  let φ := e.toMonoidHom.comp f
  have hf := planeCoreClosure_action_surjective h earlier F hm
  have hkf : IsPGroup 2 f.ker := by
    have hp := F.binaryPlaneAction_ker_isPGroup hn L h.chosen.normalizes
      (h.centralizer_LT earlier.structural)
    let j := inclusion (planeCoreClosure_le_parabolic h F)
    have hj : f.ker = (F.binaryPlaneAction hn L h.chosen.normalizes).ker.comap j := rfl
    rw [hj]
    exact hp.comap_of_injective j (inclusion_injective _)
  have hkφ : φ.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ e.injective
  have hk := ker_eq_twoCore_of_surjective_perm_three φ (e.surjective.comp hf) (hkφ ▸ hkf)
  refine ⟨?_, ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ (e.surjective.comp hf))⟩⟩
  change (pCore 2 (planeCoreClosure F)).map (planeCoreClosure F).subtype = _
  rw [← hk, hkφ, setupSeedAction_ker, subgroupOf_map_subtype, inf_comm]


/-- P₂ is an actual index-three extension of the original ambient Sylow. -/
theorem parabolic_sylow_index_three
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) : (T : Subgroup G).relIndex (F.P L) = 3 := by
  obtain ⟨_, ⟨e⟩⟩ := parabolic_plane_quotient h earlier F
  exact SymmetricThreeTwoCore.sylow_index_three e (T.subtype (sylow_le_parabolic F))

/-- The three-rank of the source plane centralizer is at most one. -/
theorem plane_centralizer_three_rank_le_one
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hm : ⁅F.Vi 2, F.H.pCoreIn 2⁆ ≠ ⊥) :
    primeRank 3 (centralizer (F.Vi 2 : Set G)) ≤ 1 := by
  let := h.chosen.elementary
  let I := planeCoreClosure F
  let C := centralizer (F.Vi 2 : Set G)
  have hIG : I ≤ F.Gi 2 := (planeCoreClosure_le_parabolic h F).trans
    (F.P_le_G₂ (by have := h.rank; omega) L h.chosen.normalizes)
  have hCG : C ≤ F.Gi 2 := Subgroup.centralizer_le_normalizer _
  have hn := (normal_subgroupOf_iff_le_normalizer hIG).mp (planeCoreClosure_normal h F)
  obtain ⟨hcore, ⟨e⟩⟩ := planeCoreClosure_quotient h earlier F hm
  have hIC : IsPGroup 2 (I ⊓ C : Subgroup G) := hcore ▸ isPGroup_pCoreIn 2 I
  have hsum := primeRank_add_le_of_normalizes_of_twoGroup_intersection
    (p := 3) (by decide) I C
    (hIG.trans (normalizer_le_normalizer_centralizer (F.Vi 2))) (hCG.trans hn) hIC
  have hnon : F.Vi 2 ≠ ⊥ := by
    intro he
    have hc := F.card 2 (by have := h.rank; omega)
    simp [he] at hc
  have htwoLocal : IsTwoLocal (F.Gi 2) :=
    ⟨F.Vi 2, hnon, (F.binaryPlane_elementary).isPGroup, rfl⟩
  have hr : primeRank 3 (F.Gi 2) ≤ 2 :=
    (CFSG.Quasithin.isQuasithin_iff_twoLocal.mp h.source.simpleQTKE.quasithin)
      _ htwoLocal 3 Nat.prime_three (by decide)
  have hup := hsum.trans ((Theory.GroupTheory.primeRank_le_of_injective 3
    (inclusion (sup_le hIG hCG)) (inclusion_injective _)).trans hr)
  have hpos : 1 ≤ primeRank 3 I := by
    rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup,
      primeRank_congr 3 e]
    let t : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
    have ht3 : t ^ 3 = 1 := by decide
    have ht : orderOf t = 3 := orderOf_eq_prime ht3 (by decide)
    let : IsElementaryAbelian 3 (zpowers t) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one ht3
    exact IsElementaryAbelian.primeRank_ge_of_card (zpowers t) (by
      simpa only [Nat.card_zpowers, pow_one] using ht)
  change primeRank 3 C ≤ 1
  omega

omit [Finite G] in
/-- Relative normality of K₁ transports its core movement to O₂(G₁). -/
theorem point_core_moves_plane_of_component
    {F : InvariantFlag T V n} (C : ComponentGeometry F L)
    (hm : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥) :
    ⁅F.Vi 2, F.H.pCoreIn 2⁆ ≠ ⊥ := by
  have hcore : C.K1.pCoreIn 2 ≤ F.H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 C.K1)
      ((pCoreIn_le 2 C.K1).trans C.point_le)
      (((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal).trans
        (normalizer_le_normalizer_characteristic_image C.K1 (pCore 2 C.K1)))
  intro he
  exact hm (le_bot_iff.mp (he ▸ commutator_mono (le_refl (F.Vi 2)) hcore))

/-- Apply 12.9.6(1) to construct every clause of 12.9.6(2–3), using the
new I₂=⟨O₂(G₁)^G₂⟩. Only the movement premise remains for the local-control owner. -/
theorem plane_local_control_of_component_movement
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hm : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥) :
    ((planeCoreClosure F).subgroupOf (F.Gi 2)).Normal ∧
      planeCoreClosure F ⊔ (T : Subgroup G) = F.P L ∧
      (T : Subgroup G).relIndex (F.P L) = 3 ∧
      (planeCoreClosure F).pCoreIn 2 = planeCoreClosure F ⊓ centralizer (F.Vi 2 : Set G) ∧
      Nonempty (((planeCoreClosure F) ⧸ pCore 2 (planeCoreClosure F)) ≃* Equiv.Perm (Fin 3)) ∧
      primeRank 3 (centralizer (F.Vi 2 : Set G)) ≤ 1 := by
  have hm' := point_core_moves_plane_of_component C hm
  obtain ⟨hk, he⟩ := planeCoreClosure_quotient h earlier F hm'
  exact ⟨planeCoreClosure_normal h F, planeCoreClosure_sup_sylow h earlier F hm',
    parabolic_sylow_index_three h earlier F, hk, he, plane_centralizer_three_rank_le_one h earlier F hm'⟩



end CFSG.Quasithin.Chapter12.Section09.NaturalSource

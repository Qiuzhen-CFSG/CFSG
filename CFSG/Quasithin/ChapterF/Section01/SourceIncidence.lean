module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Cross-normalizers and the common Borel in F.1

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed
pp.259–262, Hypothesis F.1.1 and Lemma F.1.3(2), (3), (4), (6).
We also establish the assertion S ∈ Syl₂(B) used in F.1.10(2).

Characteristic two passes from the finite parabolic to its normal local
factor Lᵢ. Its self-centralizing two-core is nontrivial. If Lⱼ normalized
Lᵢ, this core would be normal in G₀, contradicting F.1.1(e). The unique
maximal Sylow-overgroup theorem therefore identifies Bⱼ with N_{Lⱼ}(Lᵢ).
These intersection descriptions give mutual normalization of the Borels,
and their characteristic two-cores are the local Sylow subgroups.

The common Borel is a solvable normalized product. Factoring elements as
lᵢb proves both its normalizer description and the parabolic intersection.
Finally, the two local odd-index calculations and the subgroup product
index formula prove that S is an actual Sylow subgroup of B. No finiteness
of the ambient group or G₀, or ambient normality of Lᵢ, is used.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- F.1.1(f) passes to the normal subgroup Lᵢ of its own parabolic. -/
theorem HypothesisF11.local_core_selfCentralizing (h : HypothesisF11 L S) (i : Fin 2) :
    centralizer (pCore 2 (L i) : Set (L i)) ≤ pCore 2 (L i) := by
  let := h.finite_parabolic i
  let := h.local_normal_in_parabolic i
  have hc := normal_core_selfCentralizing
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two i))
    ((L i).subgroupOf (parabolic L S i))
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe (show L i ≤ parabolic L S i from
      le_sup_left.trans le_sup_left))).mp hc

/-- The nontriviality used in F.1.3(2) follows from F.1.1(f), rather than
being an additional local hypothesis. -/
theorem HypothesisF11.local_twoCore_ne_bot (h : HypothesisF11 L S) (i : Fin 2) :
    twoCore (L i) ≠ ⊥ := by
  intro he
  have he' : pCore 2 (L i) = ⊥ :=
    ((pCore 2 (L i)).map_eq_bot_iff_of_injective (L i).subtype_injective).mp he
  have hc := h.local_core_selfCentralizing i
  rw [he'] at hc
  have hL : L i ≤ borel (L i) S := by
    intro x hx
    have hx1 : (⟨x, hx⟩ : L i) = 1 := hc (by
      intro y hy
      have hy1 : y = 1 := hy
      simp only [hy1, one_mul, mul_one])
    have : x = 1 := congrArg Subtype.val hx1
    simpa only [this] using (borel (L i) S).one_mem
  exact (h.rankOneBorelFacts i).proper.not_ge hL

private theorem core_bot_of_cross_normalizes (h : HypothesisF11 L S) (i : Fin 2)
    (hn : L (other i) ≤ normalizer (L i : Set G)) : twoCore (L i) = ⊥ := by
  have hgen : generated L S ≤ normalizer (L i : Set G) := by
    fin_cases i
    · exact sup_le (sup_le (L 0).le_normalizer hn) (h.S_normalizes 0)
    · exact sup_le (sup_le hn (L 1).le_normalizer) (h.S_normalizes 1)
  have hLG : L i ≤ generated L S := by
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  have hc : twoCore (L i) ≤ (generated L S).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (pCore_isPGroup.map (L i).subtype)
      ((map_subtype_le _).trans hLG)
      (hgen.trans (normalizer_le_normalizer_characteristic_image (L i) (pCore 2 (L i))))
  simpa only [pCoreIn, h.twoCore_free, Subgroup.map_bot, le_bot_iff] using hc

/-- F.1.3(2): Bⱼ is exactly the normalizer of Lᵢ inside Lⱼ. -/
theorem lemma_F_1_3_2 (h : HypothesisF11 L S) (i : Fin 2) :
    borel (L (other i)) S = L (other i) ⊓ normalizer (L i : Set G) := by
  apply le_antisymm (le_inf (borel_le _ _) (h.cross i))
  apply (h.rankOneBorelFacts (other i)).unique_maximal
  · exact le_inf inf_le_right ((localSylow_le_borel _ _).trans (h.cross i))
  · apply lt_of_le_of_ne inf_le_left
    intro he
    have hn : L (other i) ≤ normalizer (L i : Set G) := by
      rw [← he]
      exact inf_le_right
    exact h.local_twoCore_ne_bot i (core_bot_of_cross_normalizes h i hn)
/-- The cross-normalizer descriptions imply that Bⱼ normalizes Bᵢ. -/
theorem HypothesisF11.cross_normalizes_borel (h : HypothesisF11 L S) (i : Fin 2) :
    borel (L (other i)) S ≤ normalizer (borel (L i) S : Set G) := by
  have he := lemma_F_1_3_2 h (other i)
  rw [other_other] at he
  rw [he]
  apply le_trans _ inf_normalizer_le_normalizer_inf
  exact le_inf (h.cross i) (((borel_le _ _).trans (L (other i)).le_normalizer).trans
    (normalizer (L (other i) : Set G)).le_normalizer)

/-- Bⱼ preserves Sᵢ because Sᵢ is the characteristic two-core of Bᵢ. -/
theorem HypothesisF11.cross_normalizes_localSylow (h : HypothesisF11 L S) (i : Fin 2) :
    borel (L (other i)) S ≤ normalizer ((S ⊓ L i : Subgroup G) : Set G) := by
  rw [← (h.rankOneBorelFacts i).twoCore_eq]
  exact (h.cross_normalizes_borel i).trans
    (normalizer_le_normalizer_characteristic_image _ _)

/-- F.1.3(3): the cross Borel acts on both the Borel and its local Sylow subgroup. -/
theorem lemma_F_1_3_3 (h : HypothesisF11 L S) (i : Fin 2) :
    borel (L (other i)) S ≤ normalizer (borel (L i) S : Set G) ∧
      borel (L (other i)) S ≤ normalizer ((S ⊓ L i : Subgroup G) : Set G) :=
  ⟨h.cross_normalizes_borel i, h.cross_normalizes_localSylow i⟩

/-- Each local Borel lies in the common Borel. -/
theorem borel_le_commonBorel (i : Fin 2) : borel (L i) S ≤ commonBorel L S := by
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left

/-- Both parabolics contain the common Borel. -/
theorem commonBorel_le_parabolic (i : Fin 2) : commonBorel L S ≤ parabolic L S i := by
  rw [parabolic_eq_sup_commonBorel]
  exact le_sup_right

/-- B acts on each Lᵢ, as required for the product LᵢB. -/
theorem HypothesisF11.commonBorel_normalizes_local (h : HypothesisF11 L S) (i : Fin 2) :
    commonBorel L S ≤ normalizer (L i : Set G) := by
  fin_cases i
  · exact sup_le (sup_le ((borel_le _ _).trans (L 0).le_normalizer) (h.cross 0))
      (h.S_normalizes 0)
  · exact sup_le (sup_le (h.cross 1) ((borel_le _ _).trans (L 1).le_normalizer))
      (h.S_normalizes 1)

/-- The local Borels are preserved by every factor of B. -/
theorem HypothesisF11.commonBorel_normalizes_borel (h : HypothesisF11 L S) (i : Fin 2) :
    commonBorel L S ≤ normalizer (borel (L i) S : Set G) := by
  fin_cases i
  · exact sup_le (sup_le (borel (L 0) S).le_normalizer (h.cross_normalizes_borel 0))
      (h.S_normalizes_borel 0)
  · exact sup_le (sup_le (h.cross_normalizes_borel 1) (borel (L 1) S).le_normalizer)
      (h.S_normalizes_borel 1)

/-- Relative normality of Bᵢ in B, used in the subsequent Cartan construction. -/
theorem HypothesisF11.borel_normal_in_commonBorel (h : HypothesisF11 L S) (i : Fin 2) :
    ((borel (L i) S).subgroupOf (commonBorel L S)).Normal :=
  normal_subgroupOf_of_le_normalizer (h.commonBorel_normalizes_borel i)

/-- The common Borel normalizes the actual subgroup S ∩ Lᵢ. -/
theorem HypothesisF11.commonBorel_normalizes_localSylow (h : HypothesisF11 L S) (i : Fin 2) :
    commonBorel L S ≤ normalizer ((S ⊓ L i : Subgroup G) : Set G) := by
  rw [← (h.rankOneBorelFacts i).twoCore_eq]
  exact (h.commonBorel_normalizes_borel i).trans
    (normalizer_le_normalizer_characteristic_image _ _)

/-- The join defining B is the literal source product B₁B₂S. -/
theorem HypothesisF11.commonBorel_coe_eq_mul (h : HypothesisF11 L S) :
    (commonBorel L S : Set G) =
      (borel (L 0) S : Set G) * (borel (L 1) S : Set G) * (S : Set G) := by
  have hcross : borel (L 1) S ≤ normalizer (borel (L 0) S : Set G) :=
    h.cross_normalizes_borel 0
  rw [commonBorel, coe_mul_of_right_le_normalizer_left _ _
    ((le_inf (h.S_normalizes_borel 0) (h.S_normalizes_borel 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)),
    coe_mul_of_right_le_normalizer_left _ _ hcross]

/-- F.1.3(4), solvability: successive normal solvable products give B. -/
theorem HypothesisF11.commonBorel_solvable (h : HypothesisF11 L S) :
    Group.IsSolvable (commonBorel L S) := by
  let := (h.rankOneBorelFacts 0).solvable
  let := (h.rankOneBorelFacts 1).solvable
  let := h.finite_S
  let : Group.IsNilpotent S := h.S_isP.isNilpotent
  let : Group.IsSolvable (borel (L 0) S ⊔ borel (L 1) S : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes _ _ (h.cross_normalizes_borel 0)
  exact Group.isSolvable_sup_of_normalizes _ _
    ((le_inf (h.S_normalizes_borel 0) (h.S_normalizes_borel 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))

/-- F.1.3(4), normalizer description inside the literal source parabolic. -/
theorem HypothesisF11.commonBorel_eq_normalizer (h : HypothesisF11 L S) (i : Fin 2) :
    commonBorel L S = parabolic L S i ⊓ normalizer ((S ⊓ L i : Subgroup G) : Set G) := by
  apply le_antisymm (le_inf (commonBorel_le_parabolic i) (h.commonBorel_normalizes_localSylow i))
  intro x hx
  have hxP := hx.1
  rw [parabolic_eq_sup_commonBorel] at hxP
  have hxprod : x ∈ (L i : Set G) * (commonBorel L S : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (h.commonBorel_normalizes_local i)]
    exact hxP
  obtain ⟨a, ha, b, hb, rfl⟩ := hxprod
  have haN : a ∈ normalizer ((S ⊓ L i : Subgroup G) : Set G) :=
    (normalizer _).mul_mem_cancel_right (h.commonBorel_normalizes_localSylow i hb) |>.mp hx.2
  exact (commonBorel L S).mul_mem (borel_le_commonBorel i ⟨ha, haN⟩) hb

/-- F.1.3(4): the common Borel is solvable and is the local Sylow normalizer. -/
theorem lemma_F_1_3_4 (h : HypothesisF11 L S) (i : Fin 2) :
    Group.IsSolvable (commonBorel L S) ∧
      commonBorel L S = parabolic L S i ⊓ normalizer ((S ⊓ L i : Subgroup G) : Set G) :=
  ⟨h.commonBorel_solvable, h.commonBorel_eq_normalizer i⟩

/-- F.1.3(6): the two parabolics intersect in precisely B. -/
theorem lemma_F_1_3_6 (h : HypothesisF11 L S) :
    parabolic L S 0 ⊓ parabolic L S 1 = commonBorel L S := by
  apply le_antisymm _ (le_inf (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1))
  intro x hx
  have hxP := hx.1
  rw [parabolic_eq_sup_commonBorel] at hxP
  have hxprod : x ∈ (L 0 : Set G) * (commonBorel L S : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (h.commonBorel_normalizes_local 0)]
    exact hxP
  obtain ⟨a, ha, b, hb, rfl⟩ := hxprod
  have haP : a ∈ parabolic L S 1 :=
    (parabolic L S 1).mul_mem_cancel_right (commonBorel_le_parabolic 1 hb) |>.mp hx.2
  have hn : parabolic L S 1 ≤ normalizer (L 1 : Set G) :=
    sup_le (sup_le (L 1).le_normalizer (h.S_normalizes 1)) (h.cross 1)
  have haB : a ∈ borel (L 0) S := by
    change a ∈ borel (L (other 1)) S
    rw [lemma_F_1_3_2 h 1]
    exact ⟨ha, hn haP⟩
  exact (commonBorel L S).mul_mem (borel_le_commonBorel 0 haB) hb
/-- The Sylow intersection has odd index in its local Borel. -/
theorem HypothesisF11.local_borel_odd_index (h : HypothesisF11 L S) (i : Fin 2) :
    ¬ 2 ∣ S.relIndex (borel (L i) S) := by
  let := h.finite_local i
  obtain ⟨T, hT⟩ := h.sylow i
  have hST : S.subgroupOf (L i) = (T : Subgroup (L i)) := by
    apply map_injective (L i).subtype_injective
    rw [subgroupOf_map_subtype, hT]
  have hind : ¬ 2 ∣ S.relIndex (L i) := by
    change ¬ 2 ∣ (S.subgroupOf (L i)).index
    rw [hST]
    exact T.not_dvd_index
  have hmul := relIndex_inf_mul_relIndex S (borel (L i) S) (L i)
  rw [inf_of_le_left (borel_le _ _)] at hmul
  have hinter : S ⊓ borel (L i) S = S ⊓ L i := by
    apply le_antisymm (inf_le_inf_left _ (borel_le _ _))
    exact le_inf inf_le_left (localSylow_le_borel _ _)
  rw [hinter, inf_relIndex_right] at hmul
  exact fun hd => hind (hd.trans (dvd_of_mul_right_eq _ hmul))

/-- Finiteness of B follows inside either finite parabolic. -/
theorem HypothesisF11.finite_commonBorel (h : HypothesisF11 L S) : Finite (commonBorel L S) := by
  let := h.finite_parabolic 0
  exact Finite.of_injective (inclusion (commonBorel_le_parabolic (L := L) (S := S) 0))
    (inclusion_injective _)

/-- Adjoining each local Borel preserves the odd index above S. -/
theorem HypothesisF11.commonBorel_odd_index (h : HypothesisF11 L S) :
    ¬ 2 ∣ S.relIndex (commonBorel L S) := by
  let := h.finite_commonBorel
  let := h.finite_S
  let C := borel (L 0) S ⊔ S
  have hSC : S ≤ C := le_sup_right
  have hCB : C ≤ commonBorel L S := sup_le (borel_le_commonBorel 0) le_sup_right
  let : Finite C := Finite.of_injective (inclusion hCB) (inclusion_injective hCB)
  have hSCidx : ¬ 2 ∣ S.relIndex C := by
    rw [relIndex_sup_of_normalizes _ _ (h.S_normalizes_borel 0)]
    exact h.local_borel_odd_index 0
  have hnorm : C ≤ normalizer (borel (L 1) S : Set G) :=
    sup_le (h.cross_normalizes_borel 1) (h.S_normalizes_borel 1)
  have hBC : borel (L 1) S ⊔ C = commonBorel L S := by
    dsimp [C, commonBorel]
    ac_rfl
  have hCBidx : ¬ 2 ∣ C.relIndex (commonBorel L S) := by
    rw [← hBC, relIndex_sup_of_normalizes _ _ hnorm]
    exact fun hd => h.local_borel_odd_index 1
      (hd.trans (relIndex_dvd_of_le_left _ hSC))
  rw [← relIndex_mul_relIndex S C (commonBorel L S) hSC hCB]
  exact fun hd => (Nat.prime_two.dvd_mul.mp hd).elim hSCidx hCBidx

/-- The assertion S ∈ Syl₂(B) used in F.1.10(2), with an actual Sylow witness
whose ambient image is exactly the original S. -/
theorem HypothesisF11.sylow_commonBorel (h : HypothesisF11 L S) :
    ∃ T : Sylow 2 (commonBorel L S),
      (T : Subgroup (commonBorel L S)).map (commonBorel L S).subtype = S := by
  have hp : IsPGroup 2 (S.subgroupOf (commonBorel L S)) := h.S_isP.comap_subtype
  refine ⟨hp.toSylow h.commonBorel_odd_index, ?_⟩
  exact map_subgroupOf_eq_of_le le_sup_right

end CFSG.Quasithin.ChapterF.Source

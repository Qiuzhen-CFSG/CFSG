module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.LocalStructure
public import CFSG.Quasithin.ChapterF.Section01.SourceStarredParabolic
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.SpecificGroups.SymmetricFive.SylowNormalizer
public import Theory.Quasithin.Rank
/-!
# The reduced overlap of the mixed A₅/S₃ pair

Write B for the full source overlap and R = O₂(B), embedded in the original
ambient group. DGS defines B₀ = (P₀* ∩ B)(P₁* ∩ B)R. In the mixed pair the
cubic Borel lies in R, so B₀ = B_K R. It is normal in B, has two-core R,
and [B₀:R] = 3. The A₅/S₅ alternatives for P₀/O₂(P₀) bound [B:B₀] by two.
Thus [B:R] is three or six, and |S| is |R| or 2|R|.

Replacing S by R preserves every genuine F.1.1 clause, both original local
factors, and both embedded parabolic kernels. Normality of the reduced Sylow
in its overlap excludes the S₅ quotient using its self-normalizing Sylow
subgroups. Consequently the first reduced parabolic is exactly P₀*, and
|R| = 4|O₂(P₀)|. These conclusions concern the literal local subgroups; R is
not asserted to be Sylow in their generated finite completion.

This supplies the local reduction and extension bound used before the mixed
kernel analysis. The bounds on the reduced kernel and the Borel recognition
remain unproved; this module does not assert the DGS case classification.

Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs: New Results and
Methods*, Part II, Hypothesis B, p.96, and (15.1), p.226;
Aschbacher–Smith, F.1.9–12, printed pp.261–264 of refs/quasithin.pdf.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

omit [Finite G] in
private theorem core_normalizes (A : Subgroup G) :
    A ≤ normalizer (twoCore A : Set G) :=
  A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 A))

/-- The source reduced overlap, retaining both starred factors and the whole Borel core. -/
@[expose] def mixedReducedBorel (L : Fin 2 → Subgroup G) (S : Subgroup G) : Subgroup G :=
  (starredParabolic L S 0 ⊓ commonBorel L S) ⊔
    (starredParabolic L S 1 ⊓ commonBorel L S) ⊔ twoCore (commonBorel L S)

omit [Finite G] in
private theorem localSylow_le_borel_core (h : HypothesisF11 L S) (i : Fin 2) :
    S ⊓ L i ≤ twoCore (commonBorel L S) := by
  exact le_pCoreIn_of_normalizes (h.S_isP.to_le inf_le_left)
    (inf_le_left.trans le_sup_right) (h.commonBorel_normalizes_localSylow i)

omit [Finite G] in
private theorem parabolic_core_le_borel_core (h : HypothesisF11 L S) (i : Fin 2) :
    twoCore (parabolic L S i) ≤ twoCore (commonBorel L S) := by
  exact le_pCoreIn_of_normalizes (pCore_isPGroup.map _)
    ((h.parabolic_core_le_S i).trans le_sup_right)
    ((commonBorel_le_parabolic i).trans (core_normalizes _))

theorem HypothesisF11.mixedReducedBorel_eq {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    mixedReducedBorel ![K,U] S = borel K S ⊔ twoCore (commonBorel ![K,U] S) := by
  unfold mixedReducedBorel
  rw [h.starredParabolic_borel_product 0, h.starredParabolic_borel_product 1]
  change (twoCore (parabolic ![K,U] S 0) ⊔ borel K S) ⊔
    (twoCore (parabolic ![K,U] S 1) ⊔ borel U S) ⊔ _ = _
  have hbU : borel U S ≤ twoCore (commonBorel ![K,U] S) := by
    rw [show borel U S = S ⊓ U from h.cubic_borel_eq_localSylow 1 eU]
    exact localSylow_le_borel_core h 1
  apply le_antisymm
  · exact sup_le (sup_le
      (sup_le ((parabolic_core_le_borel_core h 0).trans le_sup_right) le_sup_left)
      ((sup_le (parabolic_core_le_borel_core h 1) hbU).trans le_sup_right)) le_sup_right
  · exact sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left)) le_sup_right

theorem HypothesisF11.mixedReducedBorel_normalizes {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    commonBorel ![K,U] S ≤ normalizer (mixedReducedBorel ![K,U] S : Set G) := by
  rw [h.mixedReducedBorel_eq eU]
  exact (le_inf (h.commonBorel_normalizes_borel 0) (core_normalizes _)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit [Finite G] in
private theorem reduced_le (L : Fin 2 → Subgroup G) (S : Subgroup G) :
    mixedReducedBorel L S ≤ commonBorel L S :=
  sup_le (sup_le inf_le_right inf_le_right) (map_subtype_le _)

omit [Finite G] in
private theorem local_borel_inf_core (h : HypothesisF11 L S) (i : Fin 2) :
    borel (L i) S ⊓ twoCore (commonBorel L S) = S ⊓ L i := by
  apply le_antisymm
  · have hh := inf_pCoreIn_le_of_le 2 (borel_le_commonBorel (L := L) (S := S) i)
    change borel (L i) S ⊓ twoCore (commonBorel L S) ≤ twoCore (borel (L i) S) at hh
    rwa [(h.rankOneBorelFacts i).twoCore_eq] at hh
  · exact le_inf (localSylow_le_borel _ _) (localSylow_le_borel_core h i)

theorem HypothesisF11.mixedReducedBorel_core_index {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    (twoCore (commonBorel ![K,U] S)).relIndex (mixedReducedBorel ![K,U] S) = 3 := by
  have hn : twoCore (commonBorel ![K,U] S) ≤ normalizer (borel K S : Set G) :=
    (map_subtype_le _).trans (h.commonBorel_normalizes_borel 0)
  rw [h.mixedReducedBorel_eq eU, relIndex_sup_of_normalizes _ _ hn]
  rw [← inf_relIndex_right, inf_comm,
    show borel K S ⊓ twoCore (commonBorel ![K,U] S) = S ⊓ K from
      local_borel_inf_core h 0]
  have hm := relIndex_mul_relIndex (S ⊓ K) (borel K S) K (localSylow_le_borel _ _) (borel_le _ _)
  have hindices : (borel K S).relIndex K = 5 ∧ S.relIndex K = 15 :=
    h.a5_borel_local_indices 0 eK
  rw [hindices.1, inf_relIndex_right, hindices.2] at hm
  omega

theorem HypothesisF11.mixedReducedBorel_same_core {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    twoCore (mixedReducedBorel ![K,U] S) = twoCore (commonBorel ![K,U] S) := by
  exact le_antisymm (pCoreIn_mono_of_normalizes (reduced_le _ _)
    (h.mixedReducedBorel_normalizes eU))
    (le_pCoreIn_of_normalizes (pCore_isPGroup.map _) le_sup_right
      ((reduced_le _ _).trans (core_normalizes _)))


omit [Finite G] in
private theorem card_relIndex (A B : Subgroup G) (hAB : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  simpa only [relIndex_bot_left] using
    relIndex_mul_relIndex (⊥ : Subgroup G) A B bot_le hAB

omit [Finite G] in
private theorem mixed_starred_card {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    Nat.card (starredParabolic ![K,U] S 0) =
      60 * Nat.card (pCore 2 (parabolic ![K,U] S 0)) := by
  have he := (h.starredQuotientEquiv 0).symm.trans eK
  have hi : (pCore 2 (starredParabolic ![K,U] S 0)).index = 60 := by
    rw [index_eq_card, Nat.card_congr he.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hc : Nat.card (pCore 2 (starredParabolic ![K,U] S 0)) =
      Nat.card (pCore 2 (parabolic ![K,U] S 0)) := by
    calc
      _ = Nat.card (twoCore (starredParabolic ![K,U] S 0)) :=
        (card_map_of_injective (starredParabolic ![K,U] S 0).subtype_injective).symm
      _ = Nat.card (twoCore (parabolic ![K,U] S 0)) :=
        congrArg (fun X : Subgroup G => Nat.card X) (h.starredParabolic_same_core 0)
      _ = _ := card_map_of_injective (parabolic ![K,U] S 0).subtype_injective
  simpa only [hi, hc] using (pCore 2 (starredParabolic ![K,U] S 0)).index_mul_card.symm

theorem HypothesisF11.mixed_first_starred_index {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    (starredParabolic ![K,U] S 0).relIndex (parabolic ![K,U] S 0) = 1 ∨
      (starredParabolic ![K,U] S 0).relIndex (parabolic ![K,U] S 0) = 2 := by
  have hc := card_relIndex _ _ (starredParabolic_le (L := ![K,U]) (S := S) 0)
  rw [mixed_starred_card h eK, ← (pCore 2 (parabolic ![K,U] S 0)).index_mul_card] at hc
  have hpos := Nat.card_pos (α := pCore 2 (parabolic ![K,U] S 0))
  rcases h.mixed_first_parabolic_core_index eK eU with hi | hi
  · left
    rw [hi] at hc
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 60 * Nat.card (pCore 2 (parabolic ![K,U] S 0)) by omega)
    simpa only [mul_one] using hc
  · right
    rw [hi] at hc
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 60 * Nat.card (pCore 2 (parabolic ![K,U] S 0)) by omega)
    nlinarith only [hc]

theorem HypothesisF11.mixedReducedBorel_index_le_two {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    (mixedReducedBorel ![K,U] S).relIndex (commonBorel ![K,U] S) ≤ 2 := by
  have hidx : (starredParabolic ![K,U] S 0).relIndex (commonBorel ![K,U] S) =
      (starredParabolic ![K,U] S 0).relIndex (parabolic ![K,U] S 0) := by
    let P := parabolic ![K,U] S 0
    let A := (starredParabolic ![K,U] S 0).subgroupOf P
    let D := (commonBorel ![K,U] S).subgroupOf P
    let := h.starredParabolic_normal 0
    have he := relIndex_sup_left D A
    have hsup : A ⊔ D = ⊤ := by
      rw [← subgroupOf_sup (starredParabolic_le 0) (commonBorel_le_parabolic 0),
        h.starredParabolic_supplement 0]
      exact subgroupOf_self P
    rw [hsup, relIndex_top_right] at he
    have hmap := relIndex_map_map_of_injective A D P.subtype_injective
    rw [map_subgroupOf_eq_of_le (starredParabolic_le 0),
      map_subgroupOf_eq_of_le (commonBorel_le_parabolic 0)] at hmap
    exact hmap.trans he.symm
  have hle : (starredParabolic ![K,U] S 0 ⊓ commonBorel ![K,U] S) ≤
      mixedReducedBorel ![K,U] S := le_sup_left.trans le_sup_left
  have hi := relIndex_le_of_le_left (L := commonBorel ![K,U] S) hle index_ne_zero_of_finite
  rw [inf_relIndex_right, hidx] at hi
  rcases h.mixed_first_starred_index eK eU with he | he <;> omega


/-- The reduced overlap has normal Sylow two-subgroup and odd quotient of order three. -/
theorem HypothesisF11.mixedReducedBorel_two_closed {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    (pCore 2 (mixedReducedBorel ![K,U] S)).index = 3 := by
  have hi := h.mixedReducedBorel_core_index eK eU
  rw [← h.mixedReducedBorel_same_core eU] at hi
  have hm := relIndex_map_map_of_injective (pCore 2 (mixedReducedBorel ![K,U] S))
    ⊤ (mixedReducedBorel ![K,U] S).subtype_injective
  rw [← MonoidHom.range_eq_map, range_subtype, relIndex_top_right] at hm
  exact hm.symm.trans hi

/-- The full overlap has two-core index three or six, with no rank-two recognition premise. -/
theorem HypothesisF11.mixed_borel_core_index {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    (pCore 2 (commonBorel ![K,U] S)).index = 3 ∨
      (pCore 2 (commonBorel ![K,U] S)).index = 6 := by
  have hi := relIndex_mul_relIndex (twoCore (commonBorel ![K,U] S))
    (mixedReducedBorel ![K,U] S) (commonBorel ![K,U] S) le_sup_right (reduced_le _ _)
  rw [h.mixedReducedBorel_core_index eK eU] at hi
  have hm := relIndex_map_map_of_injective (pCore 2 (commonBorel ![K,U] S))
    ⊤ (commonBorel ![K,U] S).subtype_injective
  rw [← MonoidHom.range_eq_map, range_subtype, relIndex_top_right] at hm
  change (twoCore (commonBorel ![K,U] S)).relIndex (commonBorel ![K,U] S) = _ at hm
  rw [hm] at hi
  have hpos : 0 < (mixedReducedBorel ![K,U] S).relIndex (commonBorel ![K,U] S) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hle := h.mixedReducedBorel_index_le_two eK eU
  omega

/-- The extension from the reduced Borel multiplies its Sylow order by at most two. -/
theorem HypothesisF11.mixed_sylow_card_borel_core_cases {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Nat.card S = Nat.card (pCore 2 (commonBorel ![K,U] S)) ∨
      Nat.card S = 2 * Nat.card (pCore 2 (commonBorel ![K,U] S)) := by
  have hc := (pCore 2 (commonBorel ![K,U] S)).index_mul_card
  rw [(h.mixed_local_orders eK eU).1] at hc
  rcases h.mixed_borel_core_index eK eU with hi | hi
  · rw [hi] at hc
    exact Or.inl (by omega)
  · rw [hi] at hc
    exact Or.inr (by omega)

theorem HypothesisF11.mixed_sylow_card_le_twice_borel_core {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Nat.card S ≤ 2 * Nat.card (pCore 2 (commonBorel ![K,U] S)) := by
  rcases h.mixed_sylow_card_borel_core_cases eK eU with he | he <;> omega


omit [Finite G] in
private theorem borel_core_le_S (h : HypothesisF11 L S) :
    twoCore (commonBorel L S) ≤ S := by
  obtain ⟨T,hT⟩ := h.sylow_commonBorel
  exact (pCoreIn_le_sylow _ T).trans_eq hT

omit [Finite G] in
private theorem reduced_localSylow (h : HypothesisF11 L S) (i : Fin 2) :
    twoCore (commonBorel L S) ⊓ L i = S ⊓ L i :=
  le_antisymm (inf_le_inf_right _ (borel_core_le_S h))
    (le_inf (localSylow_le_borel_core h i) inf_le_right)

omit [Finite G] in
private theorem reduced_localBorel (h : HypothesisF11 L S) (i : Fin 2) :
    borel (L i) (twoCore (commonBorel L S)) = borel (L i) S := by
  unfold borel
  rw [reduced_localSylow h i]

omit [Finite G] in
private theorem reduced_parabolic_le (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L (twoCore (commonBorel L S)) i ≤ parabolic L S i := by
  unfold parabolic
  rw [reduced_localBorel h]
  exact sup_le_sup (sup_le_sup_left (borel_core_le_S h) _) le_rfl

/-- Replacing S by the whole Borel's two-core preserves all genuine F.1.1 clauses.
This makes no assertion that this smaller two-group is Sylow in the generated completion. -/
theorem HypothesisF11.restrict_to_borel_core (h : HypothesisF11 L S) :
    HypothesisF11 L (twoCore (commonBorel L S)) := by
  let R := twoCore (commonBorel L S)
  have hRS : R ≤ S := borel_core_le_S h
  have hRL (i : Fin 2) : R ≤ normalizer (L i : Set G) := hRS.trans (h.S_normalizes i)
  have hcross (i : Fin 2) : borel (L (other i)) R = borel (L (other i)) S :=
    reduced_localBorel h _
  have hnew_le (i : Fin 2) : parabolic L R i ≤ parabolic L S i := reduced_parabolic_le h i
  have hQnew (i : Fin 2) : twoCore (parabolic L S i) ≤ parabolic L R i :=
    (parabolic_core_le_borel_core h i).trans (le_sup_right.trans le_sup_left)
  refine ⟨inferInstance, pCore_isPGroup.map _, hRL, ?_, h.quotient, ?_, ?_, ?_⟩
  · intro i
    rw [reduced_localSylow h i]
    exact h.sylow i
  · intro i
    rw [hcross i]
    exact h.cross i
  · let M := generated L R
    let W := generated L S
    have hMW : M ≤ W := sup_le_sup_left hRS _
    have hSN : S ≤ normalizer (M : Set G) := by
      apply (le_inf ?_ ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
      · exact (le_inf (h.S_normalizes 0) (h.S_normalizes 1)).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
      · exact (le_sup_right : S ≤ commonBorel L S).trans (core_normalizes _)
    have hWN : W ≤ normalizer (M : Set G) :=
      sup_le (le_sup_left.trans M.le_normalizer) hSN
    have hc := pCoreIn_mono_of_normalizes (p := 2) hMW hWN
    change (pCore 2 M).map M.subtype ≤ (pCore 2 W).map W.subtype at hc
    rw [h.twoCore_free, Subgroup.map_bot] at hc
    exact (map_eq_bot_iff_of_injective _ M.subtype_injective).mp (eq_bot_iff.mpr hc)
  · intro i
    let P := parabolic L S i
    let D := (parabolic L R i).subgroupOf P
    have hQD : pCore 2 P ≤ D := by
      intro x hx
      exact hQnew i (mem_map_of_mem P.subtype hx)
    have hc := Theory.GroupTheory.centralizer_pCore_le_of_pCore_le D
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two i)) hQD
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe (hnew_le i))).mp hc

/-- The reduced pair has the exact overlap from DGS (15.1), not the original S. -/
theorem HypothesisF11.mixed_reduced_commonBorel {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    commonBorel ![K,U] (twoCore (commonBorel ![K,U] S)) = mixedReducedBorel ![K,U] S := by
  rw [h.mixedReducedBorel_eq eU]
  change borel K _ ⊔ borel U _ ⊔ _ = _
  rw [show borel K (twoCore (commonBorel ![K,U] S)) = borel K S from reduced_localBorel h 0,
    show borel U (twoCore (commonBorel ![K,U] S)) = borel U S from reduced_localBorel h 1]
  have hb : borel U S ≤ twoCore (commonBorel ![K,U] S) := by
    rw [show borel U S = S ⊓ U from h.cubic_borel_eq_localSylow 1 eU]
    exact localSylow_le_borel_core h 1
  rw [sup_assoc, sup_eq_right.mpr hb]


omit [Finite G] in
/-- Each reduced parabolic is normal in its original parabolic. -/
theorem HypothesisF11.borel_core_parabolic_normalizes (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L S i ≤ normalizer (parabolic L (twoCore (commonBorel L S)) i : Set G) := by
  let R := twoCore (commonBorel L S)
  have hS : S ≤ normalizer (parabolic L R i : Set G) := by
    unfold parabolic
    rw [reduced_localBorel h]
    exact (le_inf ((le_inf (h.S_normalizes i)
      ((le_sup_right : S ≤ commonBorel L S).trans (core_normalizes _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _))
      (h.S_normalizes_borel (other i))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hL : L i ≤ parabolic L R i := le_sup_left.trans le_sup_left
  have hb : borel (L (other i)) S ≤ parabolic L R i := by
    rw [← reduced_localBorel h (other i)]
    exact le_sup_right
  exact sup_le (sup_le (hL.trans (parabolic L R i).le_normalizer) hS)
    (hb.trans (parabolic L R i).le_normalizer)

omit [Finite G] in
/-- Reduction preserves the literal embedded kernels of both parabolics. -/
theorem HypothesisF11.borel_core_parabolic_same_core (h : HypothesisF11 L S) (i : Fin 2) :
    twoCore (parabolic L (twoCore (commonBorel L S)) i) = twoCore (parabolic L S i) := by
  apply le_antisymm (pCoreIn_mono_of_normalizes (reduced_parabolic_le h i)
    (h.borel_core_parabolic_normalizes i))
  exact le_pCoreIn_of_normalizes (pCore_isPGroup.map _)
    ((parabolic_core_le_borel_core h i).trans (le_sup_right.trans le_sup_left))
    ((reduced_parabolic_le h i).trans (core_normalizes _))

/-- The literal local factors of DGS (15.1) are the parabolics of the reduced pair. -/
theorem HypothesisF11.mixed_reduced_parabolic {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) (i : Fin 2) :
    parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) i =
      starredParabolic ![K,U] S i ⊔ mixedReducedBorel ![K,U] S := by
  rw [parabolic_eq_sup_commonBorel, h.mixed_reduced_commonBorel eU]
  unfold starredParabolic
  have hQ : twoCore (parabolic ![K,U] S i) ≤ mixedReducedBorel ![K,U] S :=
    (parabolic_core_le_borel_core h i).trans le_sup_right
  rw [sup_assoc, sup_eq_right.mpr (hQ.trans le_sup_right)]


private theorem s5_sylow_self_normalizing {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) (T : Sylow 2 H) :
    normalizer (T : Set H) = (T : Subgroup H) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkT : q.ker ≤ (T : Subgroup H) := hk ▸ pCore_isPGroup.le_sylow_of_normal T
  apply map_injective_of_ker_le q (hkT.trans (T : Subgroup H).le_normalizer) hkT
  change (normalizer (T : Set H)).map q = (T : Subgroup H).map q
  rw [T.normalizer_map_surjective q hq]
  exact Theory.SpecificGroups.SymmetricFive.SylowNormalizer.sylow_normalizer_eq_self
    (T.mapSurjective hq)

/-- A mixed pair with normal Sylow in its Borel has alternating, not symmetric,
first core quotient. The self-normalizing Sylow of S₅ excludes that alternative. -/
theorem HypothesisF11.mixed_first_quotient_of_borel_normalizes {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (hn : commonBorel ![K,U] S ≤ normalizer (S : Set G)) :
    Nonempty ((parabolic ![K,U] S 0 ⧸ pCore 2 (parabolic ![K,U] S 0)) ≃*
      alternatingGroup (Fin 5)) := by
  rcases h.mixed_first_parabolic_quotient eK eU with ha | es
  · exact ha
  · exfalso
    let P := parabolic ![K,U] S 0
    obtain ⟨T,hT⟩ := h.sylow_parabolic 0
    have ht : (T : Subgroup P) = S.subgroupOf P := by
      apply map_injective P.subtype_injective
      rw [map_subgroupOf_eq_of_le (show S ≤ P from le_sup_right.trans le_sup_left)]
      exact hT
    obtain ⟨es⟩ := es
    have he := s5_sylow_self_normalizing es T
    change normalizer ((T : Subgroup P) : Set P) = (T : Subgroup P) at he
    rw [ht, ← subgroupOf_normalizer_eq (show S ≤ P from le_sup_right.trans le_sup_left)] at he
    have hBS : commonBorel ![K,U] S ≤ S := by
      intro b hb
      exact he.le (show (⟨b, commonBorel_le_parabolic 0 hb⟩ : P) ∈
        (normalizer (S : Set G)).subgroupOf P from hn hb)
    have hi := h.mixed_sylow_borel_index eK eU
    rw [le_antisymm hBS le_sup_right, relIndex_self] at hi
    omega

/-- The first parabolic of the reduced pair has the original A₅ quotient.
The literal embedded kernel was preserved by reduction. -/
theorem HypothesisF11.mixed_reduced_first_quotient {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Nonempty ((parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 0 ⧸
      pCore 2 (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 0)) ≃*
      alternatingGroup (Fin 5)) := by
  apply h.restrict_to_borel_core.mixed_first_quotient_of_borel_normalizes eK eU
  rw [h.mixed_reduced_commonBorel eU]
  exact (reduced_le _ _).trans (core_normalizes _)

/-- The reduced Borel Sylow has four times the original first-core order. -/
theorem HypothesisF11.mixed_borel_core_card {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Nat.card (pCore 2 (commonBorel ![K,U] S)) =
      4 * Nat.card (pCore 2 (parabolic ![K,U] S 0)) := by
  let R := twoCore (commonBorel ![K,U] S)
  have hi : (pCore 2 (parabolic ![K,U] R 0)).index = 60 := by
    rw [index_eq_card, Nat.card_congr (h.mixed_reduced_first_quotient eK eU).some.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hc := h.restrict_to_borel_core.mixed_first_core_size_cases eK eU
  change ((pCore 2 (parabolic ![K,U] R 0)).index = 60 ∧
    Nat.card R = 4 * Nat.card (pCore 2 (parabolic ![K,U] R 0))) ∨
    ((pCore 2 (parabolic ![K,U] R 0)).index = 120 ∧
    Nat.card R = 8 * Nat.card (pCore 2 (parabolic ![K,U] R 0))) at hc
  have hR : Nat.card R = 4 * Nat.card (pCore 2 (parabolic ![K,U] R 0)) := by
    rcases hc with hc | hc
    · exact hc.2
    · omega
  have hcores := congrArg (fun A : Subgroup G => Nat.card A)
    (h.borel_core_parabolic_same_core 0)
  have hcores' : Nat.card (pCore 2 (parabolic ![K,U] R 0)) =
      Nat.card (pCore 2 (parabolic ![K,U] S 0)) := by
    change Nat.card ((pCore 2 (parabolic ![K,U] R 0)).map (parabolic ![K,U] R 0).subtype) =
      Nat.card ((pCore 2 (parabolic ![K,U] S 0)).map (parabolic ![K,U] S 0).subtype) at hcores
    simpa only [card_map_of_injective (parabolic ![K,U] R 0).subtype_injective,
      card_map_of_injective (parabolic ![K,U] S 0).subtype_injective] using hcores
  rw [hcores'] at hR
  exact (card_map_of_injective (commonBorel ![K,U] S).subtype_injective).symm.trans hR


/-- The first reduced parabolic is precisely the source starred parabolic. -/
theorem HypothesisF11.mixed_reduced_first_eq_starred {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 0 = starredParabolic ![K,U] S 0 := by
  have hle : starredParabolic ![K,U] S 0 ≤
      parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) 0 :=
    sup_le ((parabolic_core_le_borel_core h 0).trans (le_sup_right.trans le_sup_left))
      (le_sup_left.trans le_sup_left)
  symm
  apply eq_of_le_of_card_ge hle
  rw [mixed_starred_card h eK,
    (h.restrict_to_borel_core.mixed_local_orders eK eU).2.1,
    show Nat.card (twoCore (commonBorel ![K,U] S)) = Nat.card (pCore 2 (commonBorel ![K,U] S)) from
      card_map_of_injective (commonBorel ![K,U] S).subtype_injective,
    h.mixed_borel_core_card eK eU]
  omega

/-- In the mixed pair, DGS's entire reduced overlap is the first starred intersection. -/
theorem HypothesisF11.mixedReducedBorel_eq_first_intersection {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    mixedReducedBorel ![K,U] S = starredParabolic ![K,U] S 0 ⊓ commonBorel ![K,U] S := by
  apply le_antisymm _ (le_sup_left.trans le_sup_left)
  apply le_inf _ (reduced_le _ _)
  rw [← h.mixed_reduced_first_eq_starred eK eU, ← h.mixed_reduced_commonBorel eU]
  exact commonBorel_le_parabolic 0


/-- Quasithinness passes to the generated group of the literal reduced pair. -/
theorem HypothesisF11.borel_core_generated_quasithin (h : HypothesisF11 L S)
    (hqt : IsQuasithin (generated L S)) :
    IsQuasithin (generated L (twoCore (commonBorel L S))) := by
  have hle : generated L (twoCore (commonBorel L S)) ≤ generated L S :=
    sup_le_sup_left (borel_core_le_S h) _
  exact (isQuasithin_congr (subgroupOfEquivOfLe hle)).mp
    (hqt.subgroup ((generated L (twoCore (commonBorel L S))).subgroupOf (generated L S)))

end CFSG.Quasithin.ChapterF.Source

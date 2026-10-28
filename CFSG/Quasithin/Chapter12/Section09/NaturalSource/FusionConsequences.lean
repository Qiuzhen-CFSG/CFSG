module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.FusionGeometry
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport.Foundations
public import Theory.GroupTheory.IntersectingConjugateDisplacement
public import Theory.GroupTheory.CommutatorOrbitCard
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure.ConjugateSpan

/-!
# Hyperplane control and the weak-closure normalizer

Assume the actual local normalizer bounds of 12.9.7 and the abelian point
span of 12.9.4. For a hyperplane A = Vᵍ ∩ N_G(L) contained in T and moving
V, a nontrivial fixed element makes Vᵍ centralize [V,A]. Normalizer control
bounds the order of this displacement by two. Orbit-stabilizer then gives
noncyclic point stabilizers in A, contradicting the common fixed subgroup
calculation. This proves C_A(V)=1 in the moving case without weak closure.

Once W₀(T,V) centralizes V, normalizing conjugates centralize, so every
such hyperplane moves V and the full assertion of 12.9.9(2) follows.
Moreover W₀(T,V)=W₀(O₂(LT),V). The literal core is normalized by LT,
and the existing uniqueness theorem therefore gives N_G(W₀) ≤ N_G(L).
The only remaining fusion input is the source centralization of W₀.

Source: Aschbacher--Smith, 12.9.9, printed pp.862--863. The orbit count
replaces the equivalent transvection calculation in the third paragraph.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {X : Type u} [Group X] [Finite X]
variable {K : GroupClass.{u}} {T : Sylow 2 X} {L V : Subgroup X} {n : ℕ}

private theorem hyperplane_card_gt_four (h : HigherRankHypothesis K T L V n)
    (hn : n = 4 ∨ n = 5) (g : X) {A : Subgroup X}
    (hA : A ≤ conjugate V g) (hindex : A.relIndex (conjugate V g) = 2) :
    4 < Nat.card A := by
  have hcard : Nat.card (conjugate V g) = 2 ^ n := by
    change Nat.card (V.map (MulAut.conj g⁻¹).toMonoidHom) = _
    rw [card_map_of_injective (MulAut.conj _).injective, h.seed_card]
  have hc := relIndex_mul_relIndex (⊥ : Subgroup X) A (conjugate V g) bot_le hA
  simp only [relIndex_bot_left] at hc
  rw [hindex, hcard] at hc
  rcases hn with rfl | rfl <;> norm_num at hc <;> omega

/-- The moving-hyperplane part of 12.9.9(2), before using weak closure. -/
theorem hyperplane_fixed_free_of_moves
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set X)) V)
    (g : X) (hAT : conjugate V g ⊓ normalizer (L : Set X) ≤ (T : Subgroup X))
    (hindex : (conjugate V g ⊓ normalizer (L : Set X)).relIndex (conjugate V g) = 2)
    (hmoves : ⁅conjugate V g ⊓ normalizer (L : Set X), V⁆ ≠ ⊥) :
    (conjugate V g ⊓ normalizer (L : Set X)) ⊓ centralizer (V : Set X) = ⊥ := by
  let A := conjugate V g ⊓ normalizer (L : Set X)
  let W := conjugate V g
  have hAW : A ≤ W := inf_le_left
  have hAN : A ≤ normalizer (V : Set X) :=
    hAT.trans (h.sylow_normalizes_seed earlier.structural)
  have hbig : 4 < Nat.card A := hyperplane_card_gt_four h hn g hAW hindex
  have hnotM : ¬ W ≤ normalizer (L : Set X) := by
    intro hw
    have hAeq : A = W := inf_eq_left.mpr hw
    change A.relIndex W = 2 at hindex
    rw [hAeq, relIndex_self] at hindex
    omega
  obtain ⟨_, hinter, hnormal⟩ := source_intersections_of_local_geometry h earlier F hab control
  obtain ⟨_, _, hfixed⟩ := common_fixed_subgroups h earlier F hab control g hAT hmoves
  by_contra hker
  have hWker : W ⊓ centralizer (V : Set X) ≠ ⊥ := by
    intro he
    apply hker
    exact bot_unique ((inf_le_inf_right _ hAW).trans he.le)
  have hWC : W ≤ centralizer ((⁅V,A⁆ : Subgroup X) : Set X) :=
    centralizes_displacement_of_intersecting_conjugates W V A
      (intersecting_conjugates_commute_map_equiv V
        (fun x hx => by simpa only [conjugate, inv_inv] using hinter x⁻¹ (by simpa only [conjugate, inv_inv] using hx))
        (MulAut.conj g⁻¹)) hWker hAW
  have hCV : ⁅V,A⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hAN
  have hcsmall : Nat.card (⁅V,A⁆ : Subgroup X) ≤ 2 := by
    by_contra! hlarge
    exact hnotM (hWC.trans ((Subgroup.centralizer_le_normalizer _).trans
      ((hnormal _ hCV hlarge).trans (h.seed_normalizer_le earlier.structural earlier.uniqueness))))
  apply hmoves
  rw [commutator_comm]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro v hv
  let B := A ⊓ centralizer ({v} : Set X)
  have hBbig : 2 < Nat.card B := by
    have hcount := card_le_commutator_card_mul_centralizer A v
    have hcomm : ⁅A, zpowers v⁆ ≤ ⁅V,A⁆ := by
      rw [commutator_comm]
      exact commutator_mono (zpowers_le.mpr hv) le_rfl
    have hcomcard : Nat.card (⁅A, zpowers v⁆ : Subgroup X) ≤ 2 :=
      (Nat.card_le_card_of_injective (inclusion hcomm) (inclusion_injective _)).trans hcsmall
    have hccard : Nat.card ((centralizer ({v} : Set X)).subgroupOf A) = Nat.card B := by
      have he : (centralizer ({v} : Set X)).subgroupOf A = B.subgroupOf A := by
        ext x
        change _ ↔ x.val ∈ A ∧ _
        exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩
      rw [he]
      exact Nat.card_congr (subgroupOfEquivOfLe (show B ≤ A from inf_le_left)).toEquiv
    rw [hccard] at hcount
    have hcount' := hcount.trans (Nat.mul_le_mul_right (Nat.card B) hcomcard)
    omega
  have hvB : v ∈ centralizer (B : Set X) := by
    apply mem_centralizer_iff.mpr
    intro b hb
    exact mem_centralizer_singleton_iff.mp hb.2
  exact ((hfixed B inf_le_left hBbig).le ⟨hv,hvB⟩).2

/-- The literal Sylow hyperplane assertion, conditional only on W₀ centralization
and the preceding local geometry. -/
theorem hyperplanes_of_weakClosure
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set X)) V)
    (hW : ChapterE.indexedWeakClosure V (T : Subgroup X) 0 ≤ centralizer (V : Set X)) :
    SylowHyperplaneControl T L V := by
  let := h.chosen.elementary
  intro g hAT hindex
  apply hyperplane_fixed_free_of_moves h hn earlier F hab control g hAT hindex
  intro hcomm
  let A := conjugate V g ⊓ normalizer (L : Set X)
  have hbig : 2 < Nat.card A := lt_trans (by decide)
    (hyperplane_card_gt_four h hn g inf_le_left hindex)
  have hVC : V ≤ centralizer (A : Set X) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hVN : V ≤ normalizer (conjugate V g : Set X) :=
    hVC.trans ((Subgroup.centralizer_le_normalizer _).trans
      (normalizer_control_conjugate
        (fun B hB hb => subspace_normalizer_le h F
          (fun i hi hin => (control i hi hin).trans inf_le_right) hB hb)
        g A inf_le_left hbig))
  have hWC : conjugate V g ≤ centralizer (V : Set X) := by
    exact (ChapterE.conjugate_normalization_equivalences_of_weakClosure_zero
      (h.sylow_normalizes_seed earlier.structural) hW g⁻¹).2.1.mpr
        ((ChapterE.conjugate_normalization_equivalences_of_weakClosure_zero
          (h.sylow_normalizes_seed earlier.structural) hW g⁻¹).2.2.mpr hVN)
  have hWM := hWC.trans (h.seed_centralizer_le earlier.structural earlier.uniqueness)
  have he : A = conjugate V g := inf_eq_left.mpr hWM
  change A.relIndex (conjugate V g) = 2 at hindex
  rw [he, relIndex_self] at hindex
  omega

/-- The normalizer consequence in 12.9.9(1), from the original LT uniqueness. -/
theorem weakClosure_normalizer_of_centralizes
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (hW : ChapterE.indexedWeakClosure V (T : Subgroup X) 0 ≤ centralizer (V : Set X)) :
    normalizer (ChapterE.indexedWeakClosure V (T : Subgroup X) 0 : Set X) ≤
      normalizer (L : Set X) := by
  let J := L ⊔ (T : Subgroup X)
  let Q := J.pCoreIn 2
  have hQT : Q ≤ (T : Subgroup X) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le (show (T : Subgroup X) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype le_sup_right)
  have hWQ : ChapterE.indexedWeakClosure V (T : Subgroup X) 0 ≤ Q :=
    (le_inf ((ChapterE.indexedWeakClosure_le _ _ _).trans le_sup_right) hW).trans
      (h.centralizer_LT earlier.structural).le
  have he := ChapterE.weakClosure_eq_of_le_of_closure_le V Q (T : Subgroup X) 0 hQT hWQ
  apply normalizer_le_of_unique_maximalTwoLocal (J := J)
  · intro N hN hJN
    exact Set.mem_singleton_iff.mp ((h.maximal_unique earlier.structural earlier.uniqueness).2 ▸
      show N ∈ {N : Subgroup X | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup X) ≤ N}
        from ⟨hN, hJN⟩)
  · exact T.2.to_le (ChapterE.indexedWeakClosure_le _ _ _)
  · intro hbot
    exact h.chosen.ne_bot (bot_unique ((ChapterE.self_le_weakClosure_zero h.chosen.le_sylow).trans hbot.le))
  · rw [← he]
    exact (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))).trans
      (ChapterE.normalizer_le_weakClosure_normalizer V Q 0)

/-- Only W₀ centralization remains to construct the entire fusion input. -/
theorem fusionInput_of_weakClosure {K : GroupClass.{u}}
    (source : WeakClosureInput K) : FusionInput K := by
  intro X _ _ T L V n h hn earlier F hab C control
  have hw := source X T L V n h hn earlier F hab C control
  exact ⟨hw, weakClosure_normalizer_of_centralizes h earlier hw,
    hyperplanes_of_weakClosure h hn earlier F hab control.normalizers hw⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource

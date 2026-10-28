module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount
public import Theory.GroupAction.SmallQuotientCentralization

/-!
# The small-core exclusion in the binary linear-three branch

The original natural module has order 16 and lies in Q = O₂(LT). If Q has
order at most 32, then Q/V has order at most two. The literal conjugation
action is trivial on that quotient, so [Q,L] lies in V. A cubic subgroup
of the point residual fixes the original line V₁; its fixed length on Q
is therefore at most one. The actual A₄ quotient of the point residual
adds one noncentral binary chief factor, bounding the total by two.

The original two-conjugate argument gives at least three such factors.
This excludes the small-core branch directly and supplies |Q| > 32 to
the independent C₃-system construction. No block-recognition or extra
classification premise is needed for this adequate source consequence.

Source: Aschbacher--Smith, 13.7.6(1), printed p.940; the literal chief-count
lower bound is 13.7.10(8), printed p.942.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion Section05.PlaneGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The order-two quotient Q/V is centralized by the original component. -/
theorem source_small_core_commutator_le_module
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hsmall : Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 32) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ ≤ V := by
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  have hn : (V.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 X).trans d.normalizes_V)
  have hVQ : V ≤ Q := d.chosen.le_core
  have hcardV : Nat.card V = 16 := by
    rw [Nat.card_congr d.coordinate.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    decide
  have hcard : letI := hn; Nat.card (Q ⧸ V.subgroupOf Q) ≤ 2 := by
    let := hn
    have hm := card_eq_card_quotient_mul_card_subgroup (V.subgroupOf Q)
    rw [Nat.card_congr (subgroupOfEquivOfLe hVQ).toEquiv,hcardV] at hm
    change Nat.card Q ≤ 32 at hsmall
    nlinarith
  exact commutator_le_of_normalized_quotient_card_le_two L Q V
    (le_sup_left.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
    (le_sup_left.trans d.normalizes_V) hn hcard

/-- The actual fixed line bounds the cubic length on a core of order at most 32. -/
theorem source_small_core_cubic_length_le_one
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hsmall : Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 32)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (hAL : A ≤ L) (hAV₁ : A ≤ centralizer (V₁ : Set G)) :
    conjugationCubicLength A ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 1 := by
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  let := local_module_normal d
  let := local_module_elementary d
  have hVX : V ≤ X := d.chosen.le_sylow.trans le_sup_right
  have hVQ : V ≤ Q := by
    change V ≤ (pCore 2 X).map X.subtype
    have hc : V.subgroupOf X ≤ pCore 2 X :=
      le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 (V.subgroupOf X)⟩
    simpa only [map_subgroupOf_eq_of_le hVX] using map_mono (f := X.subtype) hc
  have hXQ : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hAX : A ≤ X := hAL.trans le_sup_left
  let : (V.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 X).trans d.normalizes_V)
  have he := CubicComparison.length_eq_of_commutator_le A Q V
    (IsPGroup.of_card (n := 1) (by simpa using hA)) (isPGroup_pCoreIn 2 X)
    hVQ (hAX.trans hXQ) (hAX.trans d.normalizes_V)
    ((commutator_mono le_rfl hAL).trans (source_small_core_commutator_le_module d hsmall))
  rw [←he]
  have hline : V₁ ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hi : (centralizer (A : Set G)).relIndex V ≤ 8 := by
    let C := (centralizer (A : Set G)).subgroupOf V
    have hVC : V₁.subgroupOf V ≤ C := comap_mono (le_centralizer_iff.mp hAV₁)
    have hcardC : 2 ≤ Nat.card C := by
      have hm := Nat.card_le_card_of_injective (inclusion hVC) (inclusion_injective hVC)
      rw [Nat.card_congr (subgroupOfEquivOfLe hline).toEquiv,d.line_card] at hm
      exact hm
    have hcardV : Nat.card V = 16 := by
      rw [Nat.card_congr d.coordinate.toEquiv]
      change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
        BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
      decide
    have hm := C.card_mul_index
    rw [hcardV] at hm
    change C.index ≤ 8
    nlinarith
  exact (Nat.log_mono_right (b := 4) hi).trans_eq (by decide)

/-- The marked A₄ quotient adds one factor to the small-core cubic bound. -/
theorem source_small_core_L1_chief_count_le_two
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hsmall : Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 32)
    (s : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁)
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : s.noncentralTwoCount ≤ 2 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨f,hf,hker⟩ := source_local_residual_surjection d h hU hV
  have hd : 3 ∣ Nat.card F.L₁ := by
    apply dvd_trans (b := Nat.card (alternatingGroup (Fin 4)))
    · rw [nat_card_alternatingGroup]
      norm_num
    · exact card_dvd_of_surjective f hf
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := F.L₁) 3 hd
  let A := zpowers (x : G)
  have hA : Nat.card A = 3 := by
    rw [Nat.card_zpowers,F.L₁.orderOf_coe x,hx]
  have hAJ : A ≤ F.L₁ := zpowers_le.mpr x.property
  have hAL : A ≤ L := hAJ.trans ((map_subtype_le _).trans inf_le_left)
  have hAV₁ : A ≤ centralizer (V₁ : Set G) :=
    hAJ.trans ((le_sup_left.trans h.local_le).trans h.H_centralizes)
  have hp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype
  have hAi : Nat.card (A.subgroupOf F.L₁) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hA
  have hc := CubicComparison.alternatingFour_count f hf hp (A.subgroupOf F.L₁) hAi s h0 h1
  have hl : conjugationCubicLength (A.subgroupOf F.L₁) f.ker ≤ 1 := by
    rw [hker]
    have he := CubicComparison.length_subgroupOf A (Q ⊓ F.L₁) F.L₁ hAJ inf_le_right
    rw [inf_subgroupOf_right] at he
    rw [he]
    exact (conjugationCubicLength_mono A inf_le_left).trans
      (source_small_core_cubic_length_le_one d hsmall A hA hAL hAV₁)
  omega

/-- The small-core branch contradicts the original three-factor lower bound. -/
theorem source_small_core_false
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hsmall : Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 32) : False := by
  exact source_L1_false_of_two_chief_bound d h hU hV
    (source_small_core_L1_chief_count_le_two d h hU hV hsmall)

/-- The actual nonabelian-span configuration forces the large-core branch on p.940. -/
theorem source_large_core
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    32 < Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  exact lt_of_not_ge (source_small_core_false d h hU hV)
end CFSG.Quasithin.Chapter13.Section07

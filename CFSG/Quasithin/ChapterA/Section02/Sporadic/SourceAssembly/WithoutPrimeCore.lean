module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.ResidualInputs
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.OffendingPrime
public import Theory.SpecificGroups.ONan.OddCoverLifting

/-!
# Sporadic Case II before the prime-core identity

The original counterexample forces odd center and makes its offending prime
divide the center. Thus every actual two-group center bound already excludes
the corresponding carrier. The source two-core theorem and the concrete
squarefree bounds handle J₁ and M₂₂. For J₃ and McL, the proved kernel prime
support and oddness imply three-group center. A compatible O'Nan linear lift
makes the center divide six and hence supplies the same three-group bound.

All twenty-six carriers are retained. The source reduction has no assumed
prime-group center and leaves exactly McL, O'Nan and the three Fischer groups.
Its final consumer discharges those cases from the exact independent model
inputs recorded in `ResidualInputs`. Those concrete producers remain required;
this does not assert their existence.

Source: Aschbacher–Smith A.2.10–19, printed pp.35–41.
-/

open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.WithoutPrimeCore
universe u
variable {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

public theorem center_odd_card
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G) :
    Odd (Nat.card (center G)) := by
  obtain ⟨f,hf⟩ := h.exists_surjective ih.theoremA
  have hh := h.center_preimage_odd_card ih.theoremA f hf
  rwa [h.center_preimage_eq_center ih.theoremA f hf] at hh

public theorem false_of_twoGroup_center
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (h2 : IsPGroup 2 (center G)) : False := by
  have hp := h.prime_eq_of_center_isPGroup ih.theoremA h2
  have ho := h.2.2.2.2.2.1
  rw [hp] at ho
  norm_num at ho

public theorem cover_j1
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* Janko1.Model) : False :=
  h.center_ne_bot ih.theoremA (Janko1.OddCover.center_eq_bot (lemma_A_2_10 h ih.theoremA) e)

public theorem cover_m22
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.Mathieu.M22) : False := by
  have hd := (centralQuotientCover e).kernel_card_dvd_three_of_pCore_eq_bot
    (lemma_A_2_10 h ih.theoremA)
    (by rw [_root_.Sporadic.Mathieu.m22_order]; norm_num) (by
      intro r hr hr2 hr3 hd
      let : Fact r.Prime := ⟨hr⟩
      have hpd : r ∣ Nat.card _root_.Sporadic.Mathieu.M22 :=
        (show r ∣ r ^ 2 by simp).trans hd
      have hh := (_root_.Sporadic.Mathieu.m22_prime_dvd_order_iff r).mp hpd
      have ht : r = 5 ∨ r = 7 ∨ r = 11 := by omega
      rw [_root_.Sporadic.Mathieu.m22_order] at hd
      rcases ht with rfl | rfl | rfl <;> norm_num at hd)
  rw [centralQuotientCover_ker] at hd
  have h3 : IsPGroup 3 (center G) := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hd)
  have hp3 := h.prime_eq_of_center_isPGroup ih.theoremA h3
  subst p
  exact SourceAssembly.cover_m22 h ih h3 e

public theorem cover_m11
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.Mathieu.M11) : False := by
  apply false_of_twoGroup_center h ih
  rw [← centralQuotientCover_ker e]
  exact
    _root_.Sporadic.Mathieu.SchurMultipliers.PartialInversionSource.m11_cover_kernel_isTwoGroup
      (centralQuotientCover e)

public theorem cover_m12
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.Mathieu.M12) : False := by
  apply false_of_twoGroup_center h ih
  rw [← centralQuotientCover_ker e]
  exact
    _root_.Sporadic.Mathieu.SchurMultipliers.m12_cover_kernel_isTwoGroup (centralQuotientCover e)

public theorem cover_m23
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.Mathieu.M23) : False := by
  apply false_of_twoGroup_center h ih
  rw [← centralQuotientCover_ker e]
  exact
    _root_.Sporadic.Mathieu.SchurMultipliers.PartialInversionSource.m23_cover_kernel_isTwoGroup
      (centralQuotientCover e)

public theorem cover_m24
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.Mathieu.M24) : False := by
  apply false_of_twoGroup_center h ih
  rw [← centralQuotientCover_ker e]
  exact
    _root_.Sporadic.Mathieu.SchurMultipliers.m24_cover_kernel_isTwoGroup (centralQuotientCover e)

public theorem cover_j2
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.LeechRelated.J2.Carrier) : False :=
  false_of_twoGroup_center h ih
    (Theory.SpecificGroups.J2HSMultipliers.J2.source_center_isPGroup ⟨e⟩)

public theorem cover_j4
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* Janko4.Model) : False :=
  false_of_twoGroup_center h ih (Janko4.OddPrimary.source_center_isPGroup ⟨e⟩)

public theorem cover_he
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* Held.He) : False :=
  false_of_twoGroup_center h ih (Held.OddPrimary.source_center_isPGroup ⟨e⟩)

public theorem cover_ru
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* Rudvalis.Model) : False :=
  false_of_twoGroup_center h ih (Rudvalis.Multiplier.source_center_isPGroup ⟨e⟩)

public theorem cover_hs
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.LeechRelated.HS.Carrier) : False :=
  false_of_twoGroup_center h ih
    (Theory.SpecificGroups.J2HSMultipliers.HS.center_isPGroup_of_quotient_equiv e)

public theorem cover_j3
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.Janko3.Model) : False := by
  have ho := center_odd_card h ih
  have h2 : ¬ 2 ∣ Nat.card (center G) := by obtain ⟨k,hk⟩ := ho; omega
  have h3 : IsPGroup 3 (center G) := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : (3:ℕ) ≠ 0)).mpr
    intro q hq
    obtain ⟨hq,hd,_⟩ := Nat.mem_primeFactors.mp hq
    let : Fact q.Prime := ⟨hq⟩
    have ht := _root_.Sporadic.Janko3.kernel_prime_eq_two_or_three (projection e)
      (projection_surjective e) (by rw [projection_ker]) (by simpa only [projection_ker] using hd)
    have hq3 : q = 3 := ht.resolve_left (by intro he; subst q; exact h2 hd)
    subst q
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, dvd_refl _, by decide⟩
  exact _root_.Sporadic.Janko3.not_quasithin_of_nontrivial_three_center h3
    (h.center_ne_bot ih.theoremA) e h.1

public theorem cover_mcl_of_comparison
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.LeechRelated.McL.Carrier)
    (comparison : _root_.Sporadic.LeechRelated.McL.Carrier ≃*
      Atlas.Sporadic.McLaughlin.Model) : False := by
  have ho := center_odd_card h ih
  have h2 : ¬ 2 ∣ Nat.card (center G) := by obtain ⟨k,hk⟩ := ho; omega
  let f := Theory.SpecificGroups.McLaughlin.Multiplier.sourceCover (e.trans comparison)
  have hk : f.toMonoidHom.ker = center G :=
    Theory.SpecificGroups.McLaughlin.Multiplier.sourceCover_kernel (e.trans comparison)
  have h5 := Theory.SpecificGroups.McLaughlin.Multiplier.not_five_dvd_card_kernel comparison f
  have h3 : IsPGroup 3 (center G) := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : (3:ℕ) ≠ 0)).mpr
    intro q hq
    obtain ⟨hq,hd,_⟩ := Nat.mem_primeFactors.mp hq
    have ht := Theory.SpecificGroups.McLaughlin.Multiplier.kernel_prime_support f hq (by rwa [hk])
    have hq3 : q = 3 := by
      rcases ht with he | he | he
      · subst q; exact (h2 hd).elim
      · exact he
      · subst q; exact (h5 (by rwa [hk])).elim
    subst q
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, dvd_refl _, by decide⟩
  exact cover_mcl_of_three_center h ih h3 e

public theorem cover_onan_of_compatible_lift
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* ONan.Model)
    (F : ONan.Cover.linearSubgroup →* G)
    (hF : (projection e).comp F = ONan.Cover.projection) : False := by
  -- The compatible lift already gives the sharper order-three bound.  The
  -- nontriviality instance is supplied by the counterexample's cover, so the
  -- exact-cardinality API can be applied directly at this source consumer.
  let : Nontrivial (center G) :=
    (nontrivial_iff_ne_bot _).mpr (h.center_ne_bot ih.theoremA)
  have hcard : Nat.card (center G) = 3 :=
    ONan.Cover.center_card_eq_three_of_lift e F hF
  have h3 : IsPGroup 3 (center G) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [hcard]
    exact dvd_rfl)
  have hp3 := h.prime_eq_of_center_isPGroup ih.theoremA h3
  subst p
  exact SourceAssembly.cover_onan_of_compatible_lift h ih h3 e F hF

public theorem sporadic_cover_reduction
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hspor : KnownSimple.IsSporadicCarrier (G ⧸ center G)) :
    Nonempty (G ⧸ center G ≃* _root_.Sporadic.LeechRelated.McL.Carrier) ∨
      Nonempty (G ⧸ center G ≃* ONan.Model) ∨
      Nonempty (G ⧸ center G ≃* _root_.Sporadic.Fischer.Fi22.Carrier) ∨
      Nonempty (G ⧸ center G ≃* _root_.Sporadic.Fischer.Fi23.Carrier) ∨
      Nonempty (G ⧸ center G ≃* _root_.Sporadic.Fischer.Fi24Prime.Carrier) := by
  obtain ⟨name,⟨e⟩⟩ := hspor
  have ho := center_odd_card h ih
  cases name with
  | m11 => exact (cover_m11 h ih e).elim
  | m12 => exact (cover_m12 h ih e).elim
  | m22 => exact (cover_m22 h ih e).elim
  | m23 => exact (cover_m23 h ih e).elim
  | m24 => exact (cover_m24 h ih e).elim
  | j1 => exact (cover_j1 h ih e).elim
  | j2 => exact (cover_j2 h ih e).elim
  | j3 => exact (cover_j3 h ih e).elim
  | j4 => exact (cover_j4 h ih e).elim
  | hs => exact (cover_hs h ih e).elim
  | he => exact (cover_he h ih e).elim
  | ru => exact (cover_ru h ih e).elim
  | mcl => exact Or.inl ⟨e⟩
  | suz => exact (cover_suz ih h.1 h.2.1 e).elim
  | onan => exact Or.inr (Or.inl ⟨e⟩)
  | co1 => exact (cover_co1 ih h.1 h.2.1 e).elim
  | co2 => exact (cover_co2 ih h.1 h.2.1 e).elim
  | co3 => exact (cover_co3 ih h.1 h.2.1 e).elim
  | fi22 => exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  | fi23 => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
  | fi24Prime => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))
  | hn => exact (not_quasithin_hn_cover e ho h.1).elim
  | ly => exact (cover_ly ih h.1 h.2.1 e).elim
  | th => exact (cover_th ih h.1 h.2.1 e).elim
  | babyMonster => exact (cover_babyMonster ih h.1 h.2.1 e).elim
  | monster => exact (cover_monster ih h.1 h.2.1 e ho).elim

public theorem sporadic_caseII_of_model_inputs
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hspor : KnownSimple.IsSporadicCarrier (G ⧸ center G))
    (comparison : _root_.Sporadic.LeechRelated.McL.Carrier ≃*
      Atlas.Sporadic.McLaughlin.Model)
    (hs : IsSemisimple Theory.SpecificGroups.U6Two.Carrier)
    (d23 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi23.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (hlift : ∀ e : G ⧸ center G ≃* ONan.Model,
      ∃ F : ONan.Cover.linearSubgroup →* G, (projection e).comp F = ONan.Cover.projection) :
    False := by
  rcases sporadic_cover_reduction h ih hspor with hm | hr
  · obtain ⟨e⟩ := hm
    exact cover_mcl_of_comparison h ih e comparison
  · rcases hr with ho | hr
    · obtain ⟨e⟩ := ho
      obtain ⟨F,hF⟩ := hlift e
      exact cover_onan_of_compatible_lift h ih e F hF
    · rcases hr with h22 | hr
      · obtain ⟨e⟩ := h22
        exact cover_fi22_of_semisimple ih h.1 h.2.1 e hs
      · rcases hr with h23 | h24
        · obtain ⟨e⟩ := h23
          exact cover_fischer_of_quotient_data ih h.1 h.2.1 e d23 hs
        · obtain ⟨e⟩ := h24
          exact cover_fischer_of_quotient_data ih h.1 h.2.1 e d24 hs

end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.WithoutPrimeCore

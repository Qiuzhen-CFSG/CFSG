module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Orthogonal
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.OrdinaryRootTransfer
public import Theory.Quasithin.CentralExtensionSL2Pair
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SecondSL2
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.SymplecticCover
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.UnitaryCaseII

/-!
# Ternary reduction for orthogonal central quotients

The two marked determinant-space SL₂ factors force a prime field through
the original odd center. Away from three, the ordinary root lifts and its
full centralizer image carries an actual elementary nine-subgroup, contrary
to quasithinness. The field-preserving small comparisons connect this to
the original Case II consumers. Only the ternary orthogonal cover leaves
remain; no defining-prime exclusion or quotient quasithinness is assumed.
Source: Aschbacher–Smith A.2.17, printed p.39.
-/

open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
open ClassicalOrthogonal ClassicalOrthogonal.Fundamental ClassicalOrthogonal.Fundamental.SplitOddBlocks
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  {r e : ℕ} [Fact r.Prime] [CharP F r]

public theorem orthogonal_odd_fieldExponent_eq_one_of_odd_center {n : ℕ} (hn : 3 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (hc : Nat.card F = r^e)
    (iso : G ⧸ center G ≃* POmegaOdd n F)
    (ho : Odd (Nat.card (center G))) (hqt : IsQuasithin G) : e = 1 := by
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  exact CentralExtension.fieldExponent_eq_one_of_commuting_sl2 hr2 he hc iso ho hqt
    (SplitOddCentralizers.oddLeft n (by omega))
    ((rightProjective (formB (n-2) F) (formB n F) (SplitOddCentralizers.oddCoordinates (F := F) n (by omega))).comp (MonoidHom.inl _ _))
    (SplitOddCentralizers.oddLeft_injective hn)
    (rightProjective_inl_injective (formB (n-2) F) (formB n F) (SplitOddCentralizers.oddCoordinates n (by omega)))
    (projective_two_factors_commute (formB (n-2) F) (formB n F) (SplitOddCentralizers.oddCoordinates n (by omega)))

public theorem orthogonal_plus_fieldExponent_eq_one_of_odd_center {n : ℕ} (hn : 4 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (hc : Nat.card F = r^e)
    (iso : G ⧸ center G ≃* POmegaPlus n F)
    (ho : Odd (Nat.card (center G))) (hqt : IsQuasithin G) : e = 1 := by
  let : Nonempty (ClassicalOrthogonal.Index (n-2)) := ⟨Sum.inl ⟨0,by omega⟩⟩
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  exact CentralExtension.fieldExponent_eq_one_of_commuting_sl2 hr2 he hc iso ho hqt
    (SplitOddCentralizers.plusLeft n (by omega))
    ((rightProjective (formD (n-2) F) (formD n F) (SplitOddCentralizers.plusCoordinates (F := F) n (by omega))).comp (MonoidHom.inl _ _))
    (SplitOddCentralizers.plusLeft_injective hn)
    (rightProjective_inl_injective (formD (n-2) F) (formD n F) (SplitOddCentralizers.plusCoordinates n (by omega)))
    (projective_two_factors_commute (formD (n-2) F) (formD n F) (SplitOddCentralizers.plusCoordinates n (by omega)))

public theorem orthogonal_minus_fieldExponent_eq_one_of_odd_center (s : ℕ)
    (hr : Odd r) (he : 1 ≤ e) (hc : Nat.card F = r^e)
    (iso : G ⧸ center G ≃* ClassicalGroup.POmegaMinus (s+3) F)
    (ho : Odd (Nat.card (center G))) (hqt : IsQuasithin G) : e = 1 := by
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hq : 2 < Nat.card F := MinusCentralizer.field_card_gt_two Fact.out hr
  exact CentralExtension.fieldExponent_eq_one_of_commuting_sl2 hr2 he hc iso ho hqt
    (MinusCentralizer.fundamentalHom s hq)
    ((MinusCentralizer.projectiveBlockHom s hq).comp (MonoidHom.inl _ _))
    (MinusCentralizer.fundamentalHom_injective s hq)
    (MinusCentralizer.projectiveBlockHom_inl_injective s hq)
    (MinusCentralizer.two_factors_commute s hq)

private theorem ordinary_centralQuotient_root_bound
    {H : Type*} [Group H] (hr : Odd r) (he : 1 ≤ e) (hc : Nat.card F = r^e)
    (hgt : 3 < Nat.card F) (h9 : Nat.card F ≠ 9)
    (iso : G ⧸ center G ≃* H) (hqt : IsQuasithin G)
    (j : SL(2,F) →* H) (hj : Function.Injective j) :
    primeRank 3 (centralizer (j.range : Set H)) ≤ 1 := by
  let π := iso.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hπ : Function.Surjective π := iso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπc : π.ker ≤ center G := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    change QuotientGroup.mk' (center G) x = 1
    exact iso.map_eq_one_iff.mp (MonoidHom.mem_ker.mp hx)
  exact (ordinary_root_source_bounds hr he hc hgt h9 π hπ hπc j hj hqt).2.2

private theorem cubic_pair_rank {H : Type*} [Group H] [Finite H]
    (E : Subgroup H) (hE : IsElementaryAbelian 3 E) (hc : Nat.card E = 9) :
    2 ≤ primeRank 3 H := by
  let := hE
  let : CommGroup E := IsMulCommutative.instCommGroup
  exact primeRank_ge_of_elementary_embedding
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 E)) hc E.subtype E.subtype_injective

public theorem orthogonal_odd_ordinary_central_quotient_false {n : ℕ} (hn : 3 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (hc : Nat.card F = r^e)
    (hgt : 3 < Nat.card F) (h9 : Nat.card F ≠ 9)
    (iso : G ⧸ center G ≃* POmegaOdd n F) (hqt : IsQuasithin G) : False := by
  have hu := ordinary_centralQuotient_root_bound hr he hc hgt h9 iso hqt
    (SplitOddCentralizers.oddLeft n (by omega)) (SplitOddCentralizers.oddLeft_injective hn)
  obtain ⟨E,hE,hEcard⟩ := SplitOddCentralizers.odd_residual_contains_nine (F := F) r hn
  have hl := cubic_pair_rank E hE hEcard
  have hi := Theory.GroupTheory.primeRank_le_of_injective 3
    (SplitOddCentralizers.centralizerResidual r (SplitOddCentralizers.oddFundamental (F := F) n (by omega))).subtype
    Subtype.val_injective
  change primeRank 3 _ ≤ primeRank 3 (centralizer
    ((SplitOddCentralizers.oddLeft (F := F) n (by omega)).range : Set (POmegaOdd n F))) at hi
  omega

public theorem orthogonal_plus_ordinary_central_quotient_false {n : ℕ} (hn : 4 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (hc : Nat.card F = r^e)
    (hgt : 3 < Nat.card F) (h9 : Nat.card F ≠ 9)
    (iso : G ⧸ center G ≃* POmegaPlus n F) (hqt : IsQuasithin G) : False := by
  have hu := ordinary_centralQuotient_root_bound hr he hc hgt h9 iso hqt
    (SplitOddCentralizers.plusLeft n (by omega)) (SplitOddCentralizers.plusLeft_injective hn)
  obtain ⟨E,hE,hEcard⟩ := SplitOddCentralizers.plus_residual_contains_nine (F := F) r hn
  have hl := cubic_pair_rank E hE hEcard
  have hi := Theory.GroupTheory.primeRank_le_of_injective 3
    (SplitOddCentralizers.centralizerResidual r (SplitOddCentralizers.plusFundamental (F := F) n (by omega))).subtype
    Subtype.val_injective
  change primeRank 3 _ ≤ primeRank 3 (centralizer
    ((SplitOddCentralizers.plusLeft (F := F) n (by omega)).range : Set (POmegaPlus n F))) at hi
  omega

private theorem minus_ordinary_block_obstruction (s : ℕ) (hq : 2 < Nat.card F)
    (hr : Odd r) (he : 1 ≤ e) (hc : Nat.card F = r^e)
    (hgt : 3 < Nat.card F) (h9 : Nat.card F ≠ 9)
    (iso : G ⧸ center G ≃* ClassicalGroup.POmegaMinus (s+3) F) (hqt : IsQuasithin G)
    (hE : ∃ E : Subgroup (ClassicalGroup.POmegaMinus (s+3) F),
      E ≤ (MinusCentralizer.projectiveBlockHom s hq).range ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9) : False := by
  have hu := ordinary_centralQuotient_root_bound hr he hc hgt h9 iso hqt
    (MinusCentralizer.fundamentalHom s hq) (MinusCentralizer.fundamentalHom_injective s hq)
  obtain ⟨E,hle,hE,hEcard⟩ := hE
  let := hE
  have hC := hle.trans (MinusCentralizer.projectiveBlockHom_le_centralizer s hq)
  have hb := (Theory.GroupTheory.primeRank_le_of_injective 3 (Subgroup.inclusion hC)
    (Subgroup.inclusion_injective hC)).trans hu
  have hl : 2 ≤ primeRank 3 E := by
    let : CommGroup E := IsMulCommutative.instCommGroup
    exact primeRank_ge_of_elementary_embedding
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 E)) hEcard (MonoidHom.id E) Function.injective_id
  omega

public theorem orthogonal_minus_ordinary_central_quotient_false {n : ℕ} (hn : 4 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (hc : Nat.card F = r^e)
    (hgt : 3 < Nat.card F) (h9 : Nat.card F ≠ 9)
    (iso : G ⧸ center G ≃* ClassicalGroup.POmegaMinus n F) (hqt : IsQuasithin G) : False := by
  have hq : 2 < Nat.card F := by omega
  by_cases h4 : n = 4
  · subst n
    exact minus_ordinary_block_obstruction 1 hq hr he hc hgt h9 iso hqt
      (MinusCentralizer.smallestBlock_contains_nine hr hq)
  obtain ⟨s,rfl⟩ : ∃ s, n = s+5 := ⟨n-5,by omega⟩
  exact minus_ordinary_block_obstruction (s+2) hq hr he hc hgt h9 iso hqt
    (MinusCentralizer.higherBlock_contains_nine s hq)

private theorem prime_gt_three_of_odd_ne_three (hr : Odd r) (hr3 : r ≠ 3) : 3 < r := by
  have hp := (Fact.out : r.Prime).two_le
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  omega

private theorem prime_ne_nine : r ≠ 9 := by
  intro hh
  subst r
  exact (by decide : ¬ Nat.Prime 9) Fact.out

public theorem orthogonal_odd_central_quotient_parameters {n : ℕ} (hn : 3 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (ho : Odd (Nat.card (center G))) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPOmegaOdd (G ⧸ center G) n (r^e)) : r = 3 ∧ e = 1 := by
  obtain ⟨F,hF,hfin,hc,⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have he1 := orthogonal_odd_fieldExponent_eq_one_of_odd_center hn hr he hc iso ho hqt
  refine ⟨?_,he1⟩
  subst e
  simp only [pow_one] at hc
  by_contra hr3
  exact orthogonal_odd_ordinary_central_quotient_false hn hr (by decide : 1 ≤ 1)
    (by simpa using hc) (hc ▸ prime_gt_three_of_odd_ne_three hr hr3)
    (hc ▸ prime_ne_nine) iso hqt

public theorem orthogonal_plus_central_quotient_parameters {n : ℕ} (hn : 4 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (ho : Odd (Nat.card (center G))) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPOmegaPlus (G ⧸ center G) n (r^e)) : r = 3 ∧ e = 1 := by
  obtain ⟨F,hF,hfin,hc,⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have he1 := orthogonal_plus_fieldExponent_eq_one_of_odd_center hn hr he hc iso ho hqt
  refine ⟨?_,he1⟩
  subst e
  simp only [pow_one] at hc
  by_contra hr3
  exact orthogonal_plus_ordinary_central_quotient_false hn hr (by decide : 1 ≤ 1)
    (by simpa using hc) (hc ▸ prime_gt_three_of_odd_ne_three hr hr3)
    (hc ▸ prime_ne_nine) iso hqt

public theorem orthogonal_minus_central_quotient_parameters {n : ℕ} (hn : 4 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (ho : Odd (Nat.card (center G))) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPOmegaMinus (G ⧸ center G) n (r^e)) : r = 3 ∧ e = 1 := by
  obtain ⟨d,rfl⟩ : ∃ d, n = d+3 := ⟨n-3,by omega⟩
  obtain ⟨F,hF,hfin,hc,⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have he1 := orthogonal_minus_fieldExponent_eq_one_of_odd_center d hr he hc iso ho hqt
  refine ⟨?_,he1⟩
  subst e
  simp only [pow_one] at hc
  by_contra hr3
  exact orthogonal_minus_ordinary_central_quotient_false hn hr (by decide : 1 ≤ 1)
    (by simpa using hc) (hc ▸ prime_gt_three_of_odd_ne_three hr hr3)
    (hc ▸ prime_ne_nine) iso hqt


universe u
variable {K : GroupClass.{u}} {G₀ T : Type u} [Group G₀] [Finite G₀]
  [Group T] [Finite T] [IsQuasisimple G₀] {p : ℕ}

omit [IsQuasisimple G₀] in
private theorem source_center_odd (h : CounterexampleToTheoremA K G₀ T p)
    (hP : IsPGroup p (center G₀)) : Odd (Nat.card (center G₀)) := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  obtain ⟨k,hk⟩ := hP.exists_card_eq
  rw [hk]
  exact h.2.2.2.2.2.1.pow

public theorem orthogonal_odd_caseII_parameters
    (h : CounterexampleToTheoremA K G₀ T p) (ih : TheoremsOnProperSections K G₀)
    (hP : IsPGroup p (center G₀)) {n r e : ℕ} [Fact r.Prime]
    (hn : 1 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaOdd (G₀ ⧸ center G₀) n (r^e)) :
    3 ≤ n ∧ r = 3 ∧ e = 1 := by
  have hn1 : n ≠ 1 := by
    intro h1
    subst n
    exact linear_caseII h ih hP (by decide) hr he
      (SmallIsomorphisms.isPSL_two_of_isPOmegaOdd_one model)
  have hn2 : n ≠ 2 := by
    intro h2
    subst n
    exact symplectic_caseII h ih hP (by decide) hr he
      (SmallIsomorphisms.isPSp_two_of_isPOmegaOdd_two hr.pow model)
  have hn3 : 3 ≤ n := by omega
  exact ⟨hn3,orthogonal_odd_central_quotient_parameters hn3 hr he (source_center_odd h hP) h.1 model⟩

public theorem orthogonal_minus_caseII_parameters
    (h : CounterexampleToTheoremA K G₀ T p) (ih : TheoremsOnProperSections K G₀)
    (hP : IsPGroup p (center G₀)) {n r e : ℕ} [Fact r.Prime]
    (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaMinus (G₀ ⧸ center G₀) n (r^e)) :
    3 ≤ n ∧ r = 3 ∧ e = 1 := by
  have hn2 : n ≠ 2 := by
    intro h2
    subst n
    have hm : ClassicalGroup.IsPSL (G₀ ⧸ center G₀) 2 (r^(e*2)) := by
      simpa only [pow_mul] using SmallIsomorphisms.isPSL_two_sq_of_isPOmegaMinus_two model
    exact linear_caseII h ih hP (by decide) hr (by omega) hm
  have hn3 : 3 ≤ n := by omega
  refine ⟨hn3,?_⟩
  by_cases h3 : n = 3
  · subst n
    let : IsSimpleGroup (G₀ ⧸ center G₀) := IsQuasisimple.simple
    have hp := unitary_caseII_parameters h ih hP (by decide : 2 ≤ 4) hr he
      (SmallIsomorphisms.isPSU_four_of_isPOmegaMinus_three hr.pow model)
    exact hp.2
  exact orthogonal_minus_central_quotient_parameters (by omega) hr he (source_center_odd h hP) h.1 model

omit [IsQuasisimple G₀] in
public theorem orthogonal_plus_caseII_parameters
    (h : CounterexampleToTheoremA K G₀ T p)
    (hP : IsPGroup p (center G₀)) {n r e : ℕ} [Fact r.Prime]
    (hn : 4 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaPlus (G₀ ⧸ center G₀) n (r^e)) : r = 3 ∧ e = 1 :=
  orthogonal_plus_central_quotient_parameters hn hr he (source_center_odd h hP) h.1 model

end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly

module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstRankTwo
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstExceptionalModels

/-!
# G₂ and triality rows in the first flag normalizer

Every containing first C-component centralizes V₁ and therefore meets its
faithful Cartan factor trivially. For odd degree, a primitive split prime
avoids the field automorphisms of G₂ and the complete outer order 3n of
triality. The actual tori have rank two, so the normalizer's prime residual
is the component after quotienting by its ambient two-core. Membership
lifts through the two-group supplement, contradicting the Cartan element.
For the cube-field endpoint q=8, the concrete seven-plane in ³D₄(2)
supplies the same argument. The existing cubic proof covers even degree.

The final consumer combines these exclusions with the linear, symplectic,
odd-extension, prime-field and sporadic refinements, for the literal Cartan
factor X ∩ C_{N_G(L₁)}(L₁/O₂(L₁)). Its exact remaining alternatives are the
field-four linear, square-field, signed ternary and J₁ models, or the large
Ree fixed group. The full embedding list is still an input, not a conclusion.

The preceding flag uniqueness, rank-one quotient, action, Cartan order and
faithfulness remain inputs of qt-d-1222-natural-flag-cartan, discharged by
qt-d-1222-natural-local-geometry. This relative-components owner retains
the embedding classification, Ree and remaining field-four cases, triangle,
second-component equality, and the full source-family assembly. No new
model-action or local callback is required for the exclusions proved here.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.761--762, and A.3.18, printed pp.51--53.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open ExceptionalActors

private theorem g2_primitive_mem {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (B : Subgroup H) [B.Normal]
    (hB : B.IsCComponent) {n p : ℕ} (hn : 1 < n) (hp : p.Prime)
    (ho : Odd p) (hnp : n < p) (hd : p ∣ 2 ^ n - 1)
    (hm : ClassificationModels.IsG2At (B ⧸ pCore 2 B) (2 ^ n))
    {a : H} (ha : a ^ p = 1) : a ∈ B := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := B.map q
  let eC : C ≃* Atlas.G2.Model F := (cComponentTwoCoreQuotientEquiv hB).symm.trans e
  have hz : center C = ⊥ := by
    apply bot_unique
    intro z hz
    exact eC.map_eq_one_iff.mp ((Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hlarge).le
      ((centerCongr eC) ⟨z,hz⟩).property)
  let eZ : (C ⧸ center C) ≃* Atlas.G2.Model F :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans eC
  let : IsSimpleGroup (Atlas.G2.Model F) := Atlas.G2.isSimple hlarge
  let := pCore_isNilpotent (p := 2) (G := H)
  let : Group.IsPerfect C := (hB.map_quotient _).perfect
  let : IsQuasisimple C := { simple := eZ.isSimpleGroup }
  have hC : IsComponent (H ⧸ pCore 2 H) C :=
    ⟨(hB.map_quotient _).subnormal, inferInstance⟩
  have hr : 2 ≤ primeRank p C := by
    rw [primeRank_congr p eC]
    exact g2_split_rank (hF.symm ▸ hd)
  have hb : primeRank p (H ⧸ pCore 2 H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  have hres : B.map q = primeToResidual p (H ⧸ pCore 2 H) :=
    (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual hC
      (by rw [hz,card_bot]; exact Nat.coprime_one_right p) hr hb eZ (by
        intro b _ m hm
        exact g2_primePower_inner hF hlarge hp hnp b m hm)).2
  have hbar : q a ∈ B.map q := by
    rw [hres]
    apply mem_primeToResidual_of_pow (n := 1)
    simp only [pow_one, ← map_pow, ha, map_one]
  have haJ : a ∈ B ⊔ pCore 2 H := by
    have hh : a ∈ (B.map q).comap q := hbar
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  have hi : Nat.Coprime p (B.subgroupOf (B ⊔ pCore 2 H)).index := by
    change Nat.Coprime p (B.relIndex (B ⊔ pCore 2 H))
    rw [relIndex_sup_left]
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_dvd_pow
    exact (((Nat.coprime_two_right.mpr ho).pow_right m).coprime_dvd_right hm).coprime_dvd_right
      (relIndex_dvd_card _ _)
  exact primeToResidual_le _ hi (mem_primeToResidual_of_pow (n := 1)
    (show (⟨a,haJ⟩ : ↥(B ⊔ pCore 2 H)) ^ (p ^ 1) = 1 from Subtype.ext (by simpa using ha)))

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The actual G₂ first-component row is impossible in every nonbinary degree.
For odd degree a primitive split prime avoids the field automorphisms; for
even degree the cubic residual gives the exclusion. -/
theorem first_component_not_g2
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hXcard : Nat.card X₁ = 2 ^ S.field.degree - 1)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ¬ ClassificationModels.IsG2At (K ⧸ pCore 2 K) (2 ^ S.field.degree) := by
  by_cases hn : Even S.field.degree
  · apply first_component_not_g2_of_three_dvd D S f hm hfix hK hLK hXN _ hfaith
    rw [hXcard]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff _).mpr hn
  intro hk
  obtain ⟨p,hp,hnp,ho,hd⟩ := primitive_split_prime S.nonbinary (by
    rintro he
    exact hn (he.symm ▸ (by decide : Even 6)))
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p (hXcard.symm ▸ hd)
  have haG : orderOf (a : G) = p := (orderOf_coe a).trans ha
  have hap : (a : G) ^ p = 1 := by simpa only [haG] using pow_orderOf_eq_one (a : G)
  have haK : (a : G) ∉ K := by
    intro haK
    have he : (a : G) = 1 := mem_bot.mp ((first_component_disjoint_of_faithful_cartan
      D S f hm hfix hK.1 hLK hfaith).le_bot ⟨haK,a.property⟩)
    rw [he,orderOf_one] at haG
    exact hp.ne_one haG.symm
  let H := normalizer (f.Vi 0 : Set G)
  let B := K.subgroupOf H
  let : B.Normal := hK.2
  let e : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1) (pCore_map_iso 2 _)
  have hmB : ClassificationModels.IsG2At (B ⧸ pCore 2 B) (2 ^ S.field.degree) := by
    obtain ⟨F,_,_,hF,⟨d⟩⟩ := hk
    exact ⟨F,inferInstance,inferInstance,hF,⟨e.trans d⟩⟩
  exact haK (g2_primitive_mem (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0))
    B hK.1.2 S.nonbinary hp ho hnp hd hmB (a := ⟨a,hXN a.property⟩) (Subtype.ext hap))

private theorem triality_prime_mem {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (B : Subgroup H) [B.Normal]
    (hB : B.IsCComponent) {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (ho : Odd p)
    (hrank : 2 ≤ primeRank p (Triality.Standard.BinaryCarrier n hn))
    (hcop : Nat.Coprime p (3 * n))
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (B ⧸ pCore 2 B))
    {a : H} (ha : a ^ p = 1) : a ∈ B := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n hn).mp hm
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := B.map q
  let eC : C ≃* Triality.Standard.BinaryCarrier n hn :=
    (cComponentTwoCoreQuotientEquiv hB).symm.trans e
  have hz : center C = ⊥ := by
    apply bot_unique
    intro z hz
    exact eC.map_eq_one_iff.mp ((Triality.Standard.binaryCarrier_center_eq_bot n hn).le
      ((centerCongr eC) ⟨z,hz⟩).property)
  let eZ : (C ⧸ center C) ≃* Triality.Standard.BinaryCarrier n hn :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans eC
  let := pCore_isNilpotent (p := 2) (G := H)
  let : Group.IsPerfect C := (hB.map_quotient _).perfect
  let : IsQuasisimple C := { simple := eZ.isSimpleGroup }
  have hC : IsComponent (H ⧸ pCore 2 H) C :=
    ⟨(hB.map_quotient _).subnormal, inferInstance⟩
  have hr : 2 ≤ primeRank p C := by rwa [primeRank_congr p eC]
  have hb : primeRank p (H ⧸ pCore 2 H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  have hres : B.map q = primeToResidual p (H ⧸ pCore 2 H) :=
    (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual hC
      (by rw [hz,card_bot]; exact Nat.coprime_one_right p) hr hb eZ (by
        intro b _ k hk
        exact outer_primePower_inner
          (Triality.Standard.TwoRank.Automorphisms.binary_outer_card_dvd n hn) hcop b k hk)).2
  have hbar : q a ∈ B.map q := by
    rw [hres]
    apply mem_primeToResidual_of_pow (n := 1)
    simp only [pow_one, ← map_pow, ha, map_one]
  have haJ : a ∈ B ⊔ pCore 2 H := by
    have hh : a ∈ (B.map q).comap q := hbar
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  have hi : Nat.Coprime p (B.subgroupOf (B ⊔ pCore 2 H)).index := by
    change Nat.Coprime p (B.relIndex (B ⊔ pCore 2 H))
    rw [relIndex_sup_left]
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_dvd_pow
    exact (((Nat.coprime_two_right.mpr ho).pow_right m).coprime_dvd_right hm).coprime_dvd_right
      (relIndex_dvd_card _ _)
  exact primeToResidual_le _ hi (mem_primeToResidual_of_pow (n := 1)
    (show (⟨a,haJ⟩ : ↥(B ⊔ pCore 2 H)) ^ (p ^ 1) = 1 from Subtype.ext (by simpa using ha)))

private theorem first_component_not_triality_of_rank
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    {m p : ℕ} (hmpos : 0 < m) (hp : p.Prime) (ho : Odd p) (hd : p ∣ Nat.card X₁)
    (hrank : 2 ≤ primeRank p (Triality.Standard.BinaryCarrier m hmpos))
    (hcop : Nat.Coprime p (3 * m)) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ m) (K ⧸ pCore 2 K) := by
  intro hk
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p hd
  have haG : orderOf (a : G) = p := (orderOf_coe a).trans ha
  have hap : (a : G) ^ p = 1 := by simpa only [haG] using pow_orderOf_eq_one (a : G)
  have haK : (a : G) ∉ K := by
    intro haK
    have he : (a : G) = 1 := mem_bot.mp ((first_component_disjoint_of_faithful_cartan
      D S f hm hfix hK.1 hLK hfaith).le_bot ⟨haK,a.property⟩)
    rw [he,orderOf_one] at haG
    exact hp.ne_one haG.symm
  let H := normalizer (f.Vi 0 : Set G)
  let B := K.subgroupOf H
  let : B.Normal := hK.2
  let e : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1) (pCore_map_iso 2 _)
  have hmB : Triality.Standard.IsTrialityGroupAt (2 ^ m) (B ⧸ pCore 2 B) := by
    obtain ⟨P,hP,⟨d⟩⟩ := hk
    exact ⟨P,hP,⟨e.trans d⟩⟩
  exact haK (triality_prime_mem (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0))
    B hK.1.2 hmpos hp ho hrank hcop hmB (a := ⟨a,hXN a.property⟩) (Subtype.ext hap))

/-- The same-field triality first-component row is impossible, including
odd field degrees. The literal split torus supplies rank two at a primitive
prime which avoids the full outer order, including its factor three. -/
theorem first_component_not_triality
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hXcard : Nat.card X₁ = 2 ^ S.field.degree - 1)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ S.field.degree) (K ⧸ pCore 2 K) := by
  by_cases he : Even S.field.degree
  · apply first_component_not_triality_of_three_dvd D S f hm hfix hK hLK hXN _ hfaith
      S.field.degree_pos
    rw [hXcard]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff _).mpr he
  obtain ⟨p,hp,hnp,ho,hd⟩ := primitive_split_prime S.nonbinary (by
    intro h6
    exact he (h6.symm ▸ (by decide : Even 6)))
  let : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by
    have hn := S.nonbinary
    have hn2 : S.field.degree ≠ 2 := by rintro h; exact he (h.symm ▸ (by decide : Even 2))
    omega
  apply first_component_not_triality_of_rank D S f hm hfix hK hLK hXN hfaith
    S.field.degree_pos hp ho (hXcard.symm ▸ hd) (triality_split_rank _ hd)
  exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp3)).mul_right
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt S.field.degree_pos hnp))

/-- The cube-field triality row is also impossible. At q=8 the explicit
order-49 subgroup in the genuine ³D₄(2) carrier replaces the split torus. -/
theorem first_component_not_trialityCube
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hXcard : Nat.card X₁ = 2 ^ S.field.degree - 1)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    {m : ℕ} (hmpos : 1 ≤ m) (hnm : S.field.degree = 3 * m) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ m) (K ⧸ pCore 2 K) := by
  by_cases he : Even S.field.degree
  · apply first_component_not_triality_of_three_dvd D S f hm hfix hK hLK hXN _ hfaith
      (show 0 < m by omega)
    rw [hXcard]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff _).mpr he
  by_cases hm1 : m = 1
  · subst m
    apply first_component_not_triality_of_rank D S f hm hfix hK hLK hXN hfaith
      Nat.zero_lt_one (by decide : Nat.Prime 7) (by decide) _ triality_seven_rank (by decide)
    rw [hXcard,hnm]
    decide
  obtain ⟨p,hp,hmp,ho,hd⟩ := primitive_split_prime (show 1 < m by omega) (by
    intro h
    apply he
    rw [hnm,h]
    decide)
  let : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by
    have hm2 : m ≠ 2 := by intro h; apply he; rw [hnm,h]; decide
    omega
  have hdX : p ∣ Nat.card X₁ := by
    rw [hXcard,hnm,Nat.mul_comm 3 m,pow_mul]
    exact hd.trans (Nat.sub_one_dvd_pow_sub_one _ _)
  apply first_component_not_triality_of_rank D S f hm hfix hK hLK hXN hfaith
    (show 0 < m by omega) hp ho hdX (triality_split_rank _ hd)
  exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp3)).mul_right
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hmp))



/-- The first-normalizer Lie list reduces to its field-four linear rows
or the actual large Ree fixed-group row. All G₂ and triality degrees have
been eliminated, including the cube-field endpoint. -/
theorem first_lie_overgroup_four_linear_or_ree
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hXcard : Nat.card X₁ = 2 ^ S.field.degree - 1)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : LieOvergroup (K ⧸ pCore 2 K) S.field.degree) :
    (S.field.degree = 2 ∧ (Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)) ∨
    (∃ m, 1 ≤ m ∧ S.field.degree = 2 * m + 1 ∧
      Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ pCore 2 K) m) := by
  have linear (h : Source.IsSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree)) :
      S.field.degree = 2 ∧ (Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) := by
    have hn := first_linear_overgroup_field_four D S f hm hfix hK hLK hXN hXcard hfaith h
    exact ⟨hn,by simpa only [hn, show (2 : ℕ) ^ 2 = 4 from rfl] using h⟩
  cases hk with
  | sl3 h => exact .inl (linear (.inl h))
  | psl3 h => exact .inl (linear (.inr h))
  | sp4 h => exact (first_component_not_symplectic D S f hm hfix hK hLK hXN hXcard hfaith h).elim
  | g2 h => exact (first_component_not_g2 D S f hm hfix hK hLK hXN hXcard hfaith h).elim
  | ree m hm hn h => exact .inr ⟨m,hm,hn,h⟩
  | triality h => exact (first_component_not_triality D S f hm hfix hK hLK hXN hXcard hfaith h).elim
  | trialityCube m hmpos hn h =>
    exact (first_component_not_trialityCube D S f hm hfix hK hLK hXN hXcard hfaith hmpos hn h).elim

/-- Apply the exceptional-Lie sieve to the literal Cartan factor
`X ∩ C_{N_G(L₁)}(L₁/O₂(L₁))`. Flag uniqueness supplies normalization;
no extra action-compatibility hypothesis is introduced. -/
theorem first_lie_overgroup_four_linear_or_ree_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : LieOvergroup (K ⧸ pCore 2 K) S.field.degree) :
    (S.field.degree = 2 ∧ (Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)) ∨
    (∃ m, 1 ≤ m ∧ S.field.degree = 2 * m + 1 ∧
      Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ pCore 2 K) m) :=
  first_lie_overgroup_four_linear_or_ree D S f hm hfix hK hLK
    (inf_le_left.trans (f.cartan_normalizes hu hX 0)) hXcard hfaith hk

/-- Away from field four, the complete proposed 11.1.1 embedding list
now leaves only equality or a large Ree fixed group. The embedding list
itself and removal of this Ree row remain with the relative-components owner. -/
theorem first_nonfour_component_equal_or_ree_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hn : S.field.degree ≠ 2) (hk : ComponentAlternative (f.Li 0) K S.field.degree) :
    f.Li 0 = K ∨ (∃ m, 1 ≤ m ∧ S.field.degree = 2 * m + 1 ∧
      Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ pCore 2 K) m) := by
  cases hk with
  | equal h => exact .inl h
  | four h _ => exact (hn h).elim
  | lie h =>
    rcases first_lie_overgroup_four_linear_or_ree_of_cartan D S f hu hm hfix hX hK hLK
      hXcard hfaith h with h | h
    · exact (hn h.1).elim
    · exact .inr h


/-- The complete first-normalizer embedding disjunction feeds the local
sieve in every field degree. Besides the established refinement alternatives,
only the specified field-four models and the large Ree row remain. This
retains the source's literal quotient models and Cartan centralizer. -/
theorem first_refinement_or_remaining_models_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : ComponentAlternative (f.Li 0) K S.field.degree) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree ∨
      (S.field.degree = 2 ∧ (Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 ∨
        (∃ u, Chapter1.Section02.LocalModels.IsPSLSign (K ⧸ pCore 2 K) u 3 5 ∨
          Chapter1.Section02.LocalModels.IsSLSign (K ⧸ pCore 2 K) u 3 5) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model))) ∨
      (∃ m, 1 ≤ m ∧ S.field.degree = 2 * m + 1 ∧
        Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ pCore 2 K) m) := by
  by_cases hn : S.field.degree = 2
  · rcases first_fieldFour_refinement_or_remaining_models_of_cartan D S f hu hm hfix hX hK hLK
      hXcard hfaith hn hk with h | h
    · exact .inl h
    · exact .inr (.inl ⟨hn,h⟩)
  · rcases first_nonfour_component_equal_or_ree_of_cartan D S f hu hm hfix hX hK hLK
      hXcard hfaith hn hk with h | h
    · exact .inl (.equal (by simpa using h))
    · exact .inr (.inr h)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

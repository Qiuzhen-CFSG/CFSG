module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstPrimeLinear
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SymplecticResidual
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.SpecificGroups.Triality.CubicComponentAction
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.SpecificGroups.PSL3.SplitPrimeActors
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic

/-!
# Rank-two Lie models at the first flag normalizer

The containing C-component centralizes V₁, whereas the prescribed Cartan
factor X₁ is faithful on V₁. Each prime divisor of |X₁| therefore gives an
order-prime element outside the component. Pass the component through the
literal ambient two-core quotient and apply the proved model residual
identities. Membership reflects back through the two-group supplement.

The symplectic identity excludes Sp₄(q) for every nonbinary q. The cubic
identities exclude G₂(q) and both genuine triality rows when three divides
|X₁|. For even field degree this also rules out the Ree parameter by parity,
leaving SL₃(q) or PSL₃(q). A prime greater than three dividing q−1 excludes
both linear models when q>4; the special-linear proof retains its scalar
center. Thus the even-degree Lie branch leaves exactly these linear models
at q=4. This is a reduction, not construction of the PGL₃(4) triangle.

The literal Cartan applications use X₁ = X ∩ C_{N_G(L₁)}(L₁/O₂(L₁)). The
preceding inner-Sylow flag uniqueness, L₁ quotient and action, and the
cardinality and faithfulness of X₁ remain source inputs produced by
qt-d-1222-natural-flag-cartan and discharged by the final parent
qt-d-1222-natural-local-geometry. The relative-components owner retains
the exhaustive embedding classification, odd-degree G₂/Ree/triality rows,
the field-four local refinement and triangle, second-component equality,
and full 11.1.1–11.1.3 assembly. The final consumer combines this reduction
with the already proved exceptional-prime and sporadic refinements.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.761--762, using A.3.18 on pp.51--53.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

private theorem sqtk_twoCore {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
  refine ⟨?_, hH.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hH.stronglyQuasithin p hp ho)

private theorem odd_mem_of_quotient_residual {H : Type*} [Group H] [Finite H]
    (B : Subgroup H) [B.Normal] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hres : B.map (QuotientGroup.mk' (pCore 2 H)) = primeToResidual p (H ⧸ pCore 2 H))
    {a : H} (ha : a ^ p = 1) : a ∈ B := by
  let : Fact p.Prime := ⟨hp⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have hbar : q a ∈ B.map q := by
    rw [hres]
    apply mem_primeToResidual_of_pow (n := 1)
    simp only [pow_one, ← map_pow, ha, map_one]
  have haJ : a ∈ B ⊔ pCore 2 H := by
    have hh : a ∈ (B.map q).comap q := hbar
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk'] using hh
  let J := B ⊔ pCore 2 H
  let C := B.subgroupOf J
  have hi : Nat.Coprime p C.index := by
    change Nat.Coprime p (B.relIndex (B ⊔ pCore 2 H))
    rw [relIndex_sup_left]
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_dvd_pow
    exact (((Nat.coprime_two_right.mpr ho).pow_right m).coprime_dvd_right hm).coprime_dvd_right
      (relIndex_dvd_card _ _)
  exact primeToResidual_le C hi (mem_primeToResidual_of_pow (n := 1)
    (show (⟨a,haJ⟩ : J) ^ (p ^ 1) = 1 from Subtype.ext (by simpa using ha)))

private theorem center_bot_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply bot_unique
  intro a ha
  exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨a,ha⟩).property)

private theorem symplectic_odd_mem {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (B : Subgroup H) [B.Normal]
    (hB : B.IsCComponent) {n p : ℕ} (hn : 1 < n) (hp : p.Prime)
    (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hm : Source.IsSp (B ⧸ pCore 2 B) 2 (2 ^ n))
    {a : H} (ha : a ^ p = 1) : a ∈ B := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := B.map q
  let eC : C ≃* Matrix.symplecticGroup (Fin 2) F :=
    (cComponentTwoCoreQuotientEquiv hB).symm.trans e
  have hz : center C = ⊥ := center_bot_transport eC
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
  let eZ : (C ⧸ center C) ≃* Matrix.symplecticGroup (Fin 2) F :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans eC
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup_of_card_eq_two_pow
    (show 2 ≤ n by omega) hF
  let : IsSimpleGroup (Matrix.symplecticGroup (Fin 2) F) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  let := pCore_isNilpotent (p := 2) (G := H)
  let : Group.IsPerfect C := (hB.map_quotient _).perfect
  let : IsQuasisimple C := { simple := eZ.isSimpleGroup }
  have hC : IsComponent (H ⧸ pCore 2 H) C :=
    ⟨(hB.map_quotient _).subnormal, inferInstance⟩
  apply odd_mem_of_quotient_residual B hp ho ?_ ha
  exact (ChapterA.Section03.OddPrime.SourceModels.SymplecticResidual.component_eq_primeClosure_and_residual
    (sqtk_twoCore hH) hC (by rw [hz]; exact IsPGroup.of_subsingleton 2 _) hn hp ho hF hd eZ).2

private theorem g2_cubic_mem {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (B : Subgroup H) [B.Normal]
    (hB : B.IsCComponent) {n : ℕ} (hn : 1 < n)
    (hm : ClassificationModels.IsG2At (B ⧸ pCore 2 B) (2 ^ n))
    {a : H} (ha : a ^ 3 = 1) : a ∈ B := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := B.map q
  let eC : C ≃* Atlas.G2.Model F := (cComponentTwoCoreQuotientEquiv hB).symm.trans e
  have hz : center C = ⊥ := center_bot_transport eC
    (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hlarge)
  let eZ : (C ⧸ center C) ≃* Atlas.G2.Model F :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans eC
  let : IsSimpleGroup (Atlas.G2.Model F) := Atlas.G2.isSimple hlarge
  let := pCore_isNilpotent (p := 2) (G := H)
  let : Group.IsPerfect C := (hB.map_quotient _).perfect
  let : IsQuasisimple C := { simple := eZ.isSimpleGroup }
  have hC : IsComponent (H ⧸ pCore 2 H) C :=
    ⟨(hB.map_quotient _).subnormal, inferInstance⟩
  apply odd_mem_of_quotient_residual B Nat.prime_three (by decide) ?_ ha
  exact (ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual.component_eq_primeClosure_and_residual
    (sqtk_twoCore hH) hC (by rw [hz]; exact IsPGroup.of_subsingleton 2 _) hlarge eZ).2


private theorem triality_cubic_mem {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (B : Subgroup H) [B.Normal]
    (hB : B.IsCComponent) {n : ℕ} (hn : 0 < n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (B ⧸ pCore 2 B))
    {a : H} (ha : a ^ 3 = 1) : a ∈ B := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n hn).mp hm
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := B.map q
  let eC : C ≃* Triality.Standard.BinaryCarrier n hn :=
    (cComponentTwoCoreQuotientEquiv hB).symm.trans e
  have hz : center C = ⊥ := center_bot_transport eC
    (Triality.Standard.binaryCarrier_center_eq_bot n hn)
  let eZ : (C ⧸ center C) ≃* Triality.Standard.BinaryCarrier n hn :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans eC
  let := pCore_isNilpotent (p := 2) (G := H)
  let : Group.IsPerfect C := (hB.map_quotient _).perfect
  let : IsQuasisimple C := { simple := eZ.isSimpleGroup }
  have hC : IsComponent (H ⧸ pCore 2 H) C :=
    ⟨(hB.map_quotient _).subnormal, inferInstance⟩
  apply odd_mem_of_quotient_residual B Nat.prime_three (by decide) ?_ ha
  exact (Triality.Standard.CubicComponentAction.component_eq_primeClosure_and_residual
    ((sqtk_twoCore hH).stronglyQuasithin 3 Nat.prime_three (by decide)) hC
    (by rw [hz,card_bot]; decide) n hn eZ).2

open scoped MatrixGroups in
private theorem linear_prime_residual {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) {C : Subgroup H}
    (hC : IsComponent H C) {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hp3 : 3 < p)
    (hz : Nat.Coprime p (Nat.card (center C)))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    (hd : p ∣ 2 ^ n - 1) (e : (C ⧸ center C) ≃* PSL(3,F)) :
    C = primeToResidual p H := by
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let := hC.2
  have hdF : p ∣ Nat.card F - 1 := hF.symm ▸ hd
  have hr := Matrix.PSL3.SplitPrimeRank.component_rank F C hz e (by omega) hdF
  have hb := hH.stronglyQuasithin p hp (hp.odd_of_ne_two (by omega))
  apply (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual
    hC hz hr hb e ?_).2
  intro a ha m hm
  exact Matrix.PSL3.SplitPrimeActors.inner_of_primePower hn hF hp3 hdF _
    (Theory.GroupAction.ComponentRankAction.inner_le_range C e)
    (Theory.GroupAction.ComponentRankAction.range_rank_le_two C e hz hr hb) a ha ⟨m,hm⟩

open scoped MatrixGroups in
private theorem linear_odd_mem {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (B : Subgroup H) [B.Normal]
    (hB : B.IsCComponent) {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hp3 : 3 < p) (hd : p ∣ 2 ^ n - 1)
    (hm : Source.IsSL (B ⧸ pCore 2 B) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 (2 ^ n))
    {a : H} (ha : a ^ p = 1) : a ∈ B := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := B.map q
  let := pCore_isNilpotent (p := 2) (G := H)
  apply odd_mem_of_quotient_residual B hp (hp.odd_of_ne_two (by omega)) ?_ ha
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · let eC : C ≃* SL(3,F) := (cComponentTwoCoreQuotientEquiv hB).symm.trans e
    let : IsQuasisimple C := IsQuasisimple.of_mulEquiv eC.symm
    have hC : IsComponent (H ⧸ pCore 2 H) C :=
      ⟨(hB.map_quotient _).subnormal, inferInstance⟩
    have hez : (center C).map eC.toMonoidHom = center SL(3,F) := by
      apply le_antisymm
      · rintro _ ⟨z,hz,rfl⟩
        exact ((centerCongr eC) ⟨z,hz⟩).property
      · intro z hz
        exact ⟨eC.symm z,((centerCongr eC).symm ⟨z,hz⟩).property,eC.apply_symm_apply z⟩
    let eZ : (C ⧸ center C) ≃* PSL(3,F) := QuotientGroup.congr _ _ eC hez
    have hz : Nat.Coprime p (Nat.card (center C)) := by
      rw [Nat.card_congr (centerCongr eC).toEquiv]
      apply Nat.Coprime.of_dvd_right (Matrix.SL3.card_center_dvd_three F)
      exact hp.coprime_iff_not_dvd.mpr (fun h => by
        have hh := Nat.le_of_dvd (by decide : 0 < 3) h
        omega)
    exact linear_prime_residual (sqtk_twoCore hH) hC hn hp hp3 hz hF hd eZ
  · let eC : C ≃* PSL(3,F) := (cComponentTwoCoreQuotientEquiv hB).symm.trans e
    let : IsQuasisimple C := IsQuasisimple.of_mulEquiv eC.symm
    have hC : IsComponent (H ⧸ pCore 2 H) C :=
      ⟨(hB.map_quotient _).subnormal, inferInstance⟩
    have hz : center C = ⊥ := center_bot_transport eC
      (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F))
    let eZ : (C ⧸ center C) ≃* PSL(3,F) :=
      ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans eC
    exact linear_prime_residual (sqtk_twoCore hH) hC hn hp hp3
      (by rw [hz,card_bot]; exact Nat.coprime_one_right p) hF hd eZ

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

private theorem first_exists_prime_outside
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card X₁) :
    ∃ a : G, a ∈ normalizer (f.Vi 0 : Set G) ∧ a ^ p = 1 ∧ a ∉ K := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p hd
  have haG : orderOf (a : G) = p := (orderOf_coe a).trans ha
  refine ⟨a,hXN a.property,by simpa only [haG] using pow_orderOf_eq_one (a : G),?_⟩
  intro haK
  have he : (a : G) = 1 := mem_bot.mp ((first_component_disjoint_of_faithful_cartan
    D S f hm hfix hK hLK hfaith).le_bot ⟨haK,a.property⟩)
  rw [he,orderOf_one] at haG
  exact hp.ne_one haG.symm

/-- The symplectic row cannot occur at the first flag normalizer, at any
nonbinary field degree. The faithful Cartan factor supplies an odd-prime
actor, and the actual symplectic residual absorbs it. -/
theorem first_component_not_symplectic
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hXcard : Nat.card X₁ = 2 ^ S.field.degree - 1)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ¬ Source.IsSp (K ⧸ pCore 2 K) 2 (2 ^ S.field.degree) := by
  intro hk
  have hq : 2 < 2 ^ S.field.degree :=
    (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) S.nonbinary
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show 2 ^ S.field.degree - 1 ≠ 1 by omega)
  have hoddq : Odd (2 ^ S.field.degree - 1) := by
    have he : Even (2 ^ S.field.degree) := (show Even 2 from by decide).pow_of_ne_zero
      (Nat.ne_of_gt S.field.degree_pos)
    exact (Nat.odd_sub' (show 0 < 2 ^ S.field.degree by positivity)).mpr (by simpa using he)
  have ho : Odd p := Odd.of_dvd_nat hoddq hd
  obtain ⟨a,haN,hap,haK⟩ := first_exists_prime_outside D S f hm hfix hK.1 hLK hXN hfaith hp
    (hXcard.symm ▸ hd)
  let H := normalizer (f.Vi 0 : Set G)
  let B := K.subgroupOf H
  let : B.Normal := hK.2
  let e : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1) (pCore_map_iso 2 _)
  have hmB : Source.IsSp (B ⧸ pCore 2 B) 2 (2 ^ S.field.degree) := by
    obtain ⟨F,_,_,hF,⟨d⟩⟩ := hk
    exact ⟨F,inferInstance,inferInstance,hF,⟨e.trans d⟩⟩
  exact haK (symplectic_odd_mem (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0))
    B hK.1.2 S.nonbinary hp ho hd hmB (a := ⟨a,haN⟩) (Subtype.ext hap))

/-- A cubic in the faithful Cartan factor excludes the G₂ row of the
first normalizer. The full intrinsic two-core quotient is retained. -/
theorem first_component_not_g2_of_three_dvd
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hthree : 3 ∣ Nat.card X₁)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ¬ ClassificationModels.IsG2At (K ⧸ pCore 2 K) (2 ^ S.field.degree) := by
  intro hk
  obtain ⟨a,haN,hap,haK⟩ := first_exists_prime_outside D S f hm hfix hK.1 hLK hXN hfaith
    Nat.prime_three hthree
  let H := normalizer (f.Vi 0 : Set G)
  let B := K.subgroupOf H
  let : B.Normal := hK.2
  let e : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1) (pCore_map_iso 2 _)
  have hmB : ClassificationModels.IsG2At (B ⧸ pCore 2 B) (2 ^ S.field.degree) := by
    obtain ⟨F,_,_,hF,⟨d⟩⟩ := hk
    exact ⟨F,inferInstance,inferInstance,hF,⟨e.trans d⟩⟩
  exact haK (g2_cubic_mem (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0))
    B hK.1.2 S.nonbinary hmB (a := ⟨a,haN⟩) (Subtype.ext hap))


/-- The genuine triality quotient is likewise impossible when the faithful
Cartan factor contains a cubic. The quotient parameter may be the same
field or its source-prescribed cubic subfield. -/
theorem first_component_not_triality_of_three_dvd
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hthree : 3 ∣ Nat.card X₁)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    {m : ℕ} (hmpos : 0 < m) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ m) (K ⧸ pCore 2 K) := by
  intro hk
  obtain ⟨a,haN,hap,haK⟩ := first_exists_prime_outside D S f hm hfix hK.1 hLK hXN hfaith
    Nat.prime_three hthree
  let H := normalizer (f.Vi 0 : Set G)
  let B := K.subgroupOf H
  let : B.Normal := hK.2
  let e : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1) (pCore_map_iso 2 _)
  have hmB : Triality.Standard.IsTrialityGroupAt (2 ^ m) (B ⧸ pCore 2 B) := by
    obtain ⟨P,hP,⟨d⟩⟩ := hk
    exact ⟨P,hP,⟨e.trans d⟩⟩
  exact haK (triality_cubic_mem (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0))
    B hK.1.2 hmpos hmB (a := ⟨a,haN⟩) (Subtype.ext hap))

/-- For even field degree the characteristic-two first-normalizer list
reduces to its two actual degree-three linear models. In particular this
removes every non-linear Lie row at field four. -/
theorem first_even_lie_overgroup_linear
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hXcard : Nat.card X₁ = 2 ^ S.field.degree - 1)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (heven : Even S.field.degree) (hk : LieOvergroup (K ⧸ pCore 2 K) S.field.degree) :
    Source.IsSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) := by
  have hd : 3 ∣ Nat.card X₁ := by
    rw [hXcard]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff _).mpr heven
  cases hk with
  | sl3 h => exact .inl h
  | psl3 h => exact .inr h
  | sp4 h => exact (first_component_not_symplectic D S f hm hfix hK hLK hXN hXcard hfaith h).elim
  | g2 h => exact (first_component_not_g2_of_three_dvd D S f hm hfix hK hLK hXN hd hfaith h).elim
  | ree m _ hn _ =>
    obtain ⟨k,hk⟩ := heven
    omega
  | triality h => exact (first_component_not_triality_of_three_dvd D S f hm hfix hK hLK hXN hd
      hfaith S.field.degree_pos h).elim
  | trialityCube m hmpos _ h => exact (first_component_not_triality_of_three_dvd D S f hm hfix
      hK hLK hXN hd hfaith (by omega) h).elim

/-- Apply the even-degree sieve to the literal X₁ = C_X(L₁/O₂(L₁)).
Its normalization follows from the original Hall Cartan and flag uniqueness. -/
theorem first_even_lie_overgroup_linear_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (heven : Even S.field.degree) (hk : LieOvergroup (K ⧸ pCore 2 K) S.field.degree) :
    Source.IsSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) :=
  first_even_lie_overgroup_linear D S f hm hfix hK hLK
    (inf_le_left.trans (f.cartan_normalizes hu hX 0)) hXcard hfaith heven hk


/-- A first-normalizer linear Lie row forces q=4. For q>4 an odd prime
p>3 divides q−1; the split torus and its actual automorphism action force
the containing component to absorb the faithful Cartan p-element. -/
theorem first_linear_overgroup_field_four
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hXcard : Nat.card X₁ = 2 ^ S.field.degree - 1)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : Source.IsSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree)) :
    S.field.degree = 2 := by
  by_contra hn
  have hlarge : 3 ≤ S.field.degree := by have := S.nonbinary; omega
  have hex : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ S.field.degree - 1 := by
    by_cases hthree : S.field.degree = 3
    · refine ⟨7,by decide,by decide,?_⟩
      rw [hthree]
      decide
    · exact Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub (by omega)
  obtain ⟨p,hp,hp3,hd⟩ := hex
  obtain ⟨a,haN,hap,haK⟩ := first_exists_prime_outside D S f hm hfix hK.1 hLK hXN hfaith hp
    (hXcard.symm ▸ hd)
  let H := normalizer (f.Vi 0 : Set G)
  let B := K.subgroupOf H
  let : B.Normal := hK.2
  let e : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1) (pCore_map_iso 2 _)
  have hmB : Source.IsSL (B ⧸ pCore 2 B) 3 (2 ^ S.field.degree) ∨
      ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 (2 ^ S.field.degree) := by
    rcases hk with ⟨F,_,_,hF,⟨d⟩⟩ | ⟨F,_,_,hF,⟨d⟩⟩
    · exact .inl ⟨F,inferInstance,inferInstance,hF,⟨e.trans d⟩⟩
    · exact .inr ⟨F,inferInstance,inferInstance,hF,⟨e.trans d⟩⟩
  exact haK (linear_odd_mem (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0))
    B hK.1.2 S.field.degree_pos hp hp3 hd hmB (a := ⟨a,haN⟩) (Subtype.ext hap))

/-- The entire even-degree characteristic-two branch is reduced to actual
SL₃(4) or PSL₃(4). This precedes, and does not assume, the PGL₃(4) triangle. -/
theorem first_even_lie_overgroup_four_linear_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (heven : Even S.field.degree) (hk : LieOvergroup (K ⧸ pCore 2 K) S.field.degree) :
    S.field.degree = 2 ∧ (Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) := by
  have hlin := first_even_lie_overgroup_linear_of_cartan D S f hu hm hfix hX hK hLK
    hXcard hfaith heven hk
  have hn := first_linear_overgroup_field_four D S f hm hfix hK hLK
    (inf_le_left.trans (f.cartan_normalizes hu hX 0)) hXcard hfaith hlin
  exact ⟨hn,by simpa only [hn,show (2 : ℕ) ^ 2 = 4 from rfl] using hlin⟩


/-- The actual field-four embedding alternatives now leave only the two
linear Lie models and the three unresolved cross-characteristic classes,
besides the already proved first-normalizer refinements. -/
theorem first_fieldFour_refinement_or_remaining_models_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hfour : S.field.degree = 2) (hk : ComponentAlternative (f.Li 0) K S.field.degree) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree ∨
      Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 ∨
      (∃ u, Chapter1.Section02.LocalModels.IsPSLSign (K ⧸ pCore 2 K) u 3 5 ∨
        Chapter1.Section02.LocalModels.IsSLSign (K ⧸ pCore 2 K) u 3 5) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  cases hk with
  | equal he => exact .inl (.equal (by simpa using he))
  | lie h =>
    obtain ⟨_,hlin⟩ := first_even_lie_overgroup_four_linear_of_cartan D S f hu hm hfix hX hK hLK
      hXcard hfaith (hfour.symm ▸ (by decide : Even 2)) h
    rcases hlin with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  | four _ h =>
    rcases first_fieldFour_refinement_or_three_rows_of_cartan D S f hu hm hfix hX hK hLK
      hXcard hfaith hfour h with h | h
    · exact .inl h
    · exact .inr (.inr (.inr h))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

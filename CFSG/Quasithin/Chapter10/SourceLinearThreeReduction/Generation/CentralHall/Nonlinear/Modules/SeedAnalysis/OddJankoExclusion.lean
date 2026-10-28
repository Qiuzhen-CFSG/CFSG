module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OriginalComponent
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.EvenConstituent
public import Theory.SpecificGroups.PSL2.PrimeCubicRank
public import Theory.Representation.NormalConstituentDisplacement
public import Theory.Representation.BinaryPrimeDegree
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# Excluding the original odd-prime and Janko component rows

The three-divisible component quotient acts faithfully on every starred
actor, so its automorphism group bounds the actor rank. Every Janko
constituent has degree at least eighteen, while an actor moves at most six
dimensions. Every odd-prime PSL2 constituent has degree at least five,
while an actor moves at most four. Thus the chosen constituent is invariant,
and the existing constituent ratio bounds contradict the original cubic
bound. Neither moved minimality nor an invariant constituent is assumed.

The final theorems apply to the literal Hall subgroup. The genuine source
catalogue is reduced to even-linear and Suzuki quotients; the even-linear
branch retains only nonseparated constituent/tensor configurations. Their
ambient exclusion and Suzuki moved minimality remain with this source owner.
Source: Aschbacher--Smith D.3.9, D.3.21, 10.1.1 and 10.2.3,
printed pp.199--207,741,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance oddJankoExclusionElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance oddJankoExclusionFiniteDimensional : FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  Module.Finite.of_finite

private theorem invariant_constituent_qhat_of_degree
    {J V : Type*} [Group J] [Finite J]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) J V) (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (S : Subgroup J) [S.Normal] [IsSimpleGroup S] [IsQuasisimple S]
    (A : Subgroup J) (hA : A ∈ ChapterD.QhatStar ρ) (hsmall : cubicRatio ρ ≤ 2)
    (hmove : ¬ A ≤ centralizer (S : Set J))
    (U : Subrepresentation (ρ.comp S.subtype)) (hU : U.toRepresentation.IsIrreducible)
    (hdegree : 2 * rank A < Module.finrank (ZMod 2) U.toSubmodule) :
    restrictedSubgroup ρ U.toSubmodule A ∈
      ChapterD.Qhat (subspaceImageRepresentation ρ U.toSubmodule) := by
  have hb := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hsmall)
  have hstable : A ≤ subspaceStabilizer ρ U.toSubmodule := by
    intro a ha
    apply (subspace_map_eq_iff ρ U.toSubmodule a).mp
    exact map_constituent_eq_self_of_displacement_lt ρ S a U hU
      ((NaturalTensor.operatorFixedCodim_le_fixedCodim ρ A ha).trans hb |>.trans_lt hdegree)
  have hgen : ⁅S,A⁆ = S := IsComponent.commutator_eq_self_of_normalizes
    (show IsComponent J S from ⟨(inferInstance : S.Normal).isSubnormal,inferInstance⟩)
    (by rw [normalizer_eq_top]; exact le_top) (by
      intro he
      exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)))
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi S
    ((Subgroup.nontrivial_iff_ne_bot S).mp inferInstance)
  have hSU : S ≤ subspaceStabilizer ρ U.toSubmodule :=
    le_subspaceStabilizer ρ _ (fun s hs v hv => U.apply_mem_toSubmodule ⟨s,hs⟩ hv)
  have hnfix : ¬ U.toSubmodule ≤ fixedSpace ρ A := by
    intro hh
    have hz := le_fixedSpace_commutator_of_invariant ρ hSU hh
    rw [hgen,hfix] at hz
    exact ((Subrepresentation.irreducible_iff_isAtom U).mp hU).ne_bot
      (Subrepresentation.toSubmodule_injective (bot_unique hz))
  have hR := ChapterD.RPlusBound.restricted ρ
    (show A ∈ ChapterD.RPlusBound ρ 2 from
      ⟨⟨hA.1.2.1,hA.1.2.2.2.le.trans hsmall⟩,ChapterD.QhatStar.mem_RPlus ρ hA⟩)
    U.toSubmodule hstable hnfix
  exact ⟨hR.1,ChapterD.isCubic_restrictedSubgroup ρ U.toSubmodule hA.1.2.2.1,hR.2⟩

private theorem original_starred_rank_and_movement
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D))) :
    rank A ≤ primeRank 2 (MulAut (L ⧸ pCore 2 L)) ∧
      ¬ A ≤ centralizer (movedStabilizerComponentImage D :
        Set (actionImage (movedStabilizerAction D))) := by
  let α := originalMovedQuotientAction D c.nonnormal
  have hfA := original_three_divisible_starred_actor_faithful D c ht htn hsep hd A hA
  constructor
  · let : IsElementaryAbelian 2 A := hA.1.2.1.2
    have hr : rank A ≤ primeRank 2 A := by
      have hc := (primeRank_le_iff_elementary_card_le (p := 2) A).mp le_rfl ⊤
        (IsElementaryAbelian.of_injective (p := 2)
          (⊤ : Subgroup A).subtype Subtype.val_injective)
      rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv,
        hA.1.2.1.card_eq_two_pow_rank] at hc
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
    exact hr.trans (Theory.GroupTheory.primeRank_le_of_injective 2 _ hfA)
  · intro hc
    apply hA.1.2.1.1
    apply bot_unique
    intro a ha
    have hk : α a = 1 := (originalMovedQuotientAction_kernel D c.nonnormal).ge (hc ha)
    exact congrArg (fun a : A => (a : actionImage (movedStabilizerAction D)))
      (hfA (show α.comp A.subtype ⟨a,ha⟩ = α.comp A.subtype 1 from hk.trans (map_one _).symm))

private theorem janko_automorphism_rank : primeRank 2 (MulAut Janko1.Model) ≤ 3 := by
  let e := MulEquiv.ofBijective (MulAut.conj : Janko1.Model →* MulAut Janko1.Model)
    ⟨MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect,
      Janko1.OuterCertificate.aut_inner⟩
  have hc : Nat.card (MulAut Janko1.Model) = 175560 :=
    (Nat.card_congr e.toEquiv).symm.trans Janko1.card_model
  apply primeRank_le_of_prime_pow_not_dvd
  rw [hc]
  norm_num

private theorem janko_prime_degree : orderOf (2 : ZMod 19) = 18 := by
  apply (orderOf_eq_iff (by decide : 0 < 18)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

/-- The original Janko row is impossible without any moved-minimality premise. -/
theorem original_janko_excluded
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* Janko1.Model) : False := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_janko D c e ht htn
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let S := movedStabilizerComponentImage D
  let eS := (originalMovedComponentEquiv D c.nonnormal).trans e
  let := D.quasisimple
  let : IsSimpleGroup S := eS.isSimpleGroup
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv (originalMovedComponentEquiv D c.nonnormal).symm
  have hi : σ.IsIrreducible := imageRepresentation_isIrreducible ρ
    (movedStabilizerAction_irreducible D c ht htn hsep)
  have hsmall := movedStabilizerAction_cubic_bound D c ht htn hsep
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff σ).mpr hsmall
  have h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,Janko1.card_model]
    norm_num
  obtain ⟨hr,hm⟩ := original_starred_rank_and_movement D c ht htn hsep h3 A hA
  have hr3 : rank A ≤ 3 := by
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    exact hr.trans janko_automorphism_rank
  obtain ⟨U,hU,hfU⟩ := exists_faithful_normal_simple_constituent σ
    (imageRepresentation_injective ρ) hi S
  have hd : 18 ≤ Module.finrank (ZMod 2) U.toSubmodule := by
    rw [←janko_prime_degree]
    apply BinaryPrimeDegree.orderOf_le_finrank U.toRepresentation hfU (by decide) (by decide)
    rw [Nat.card_congr eS.toEquiv,Janko1.card_model]
    norm_num
  have hC := invariant_constituent_qhat_of_degree σ (imageRepresentation_injective ρ) hi
    S A hA hsmall hm U hU (by omega)
  have hS := (original_component_quotient_sqtk D).knownSimple_of_equiv
    (originalMovedComponentEquiv D c.nonnormal).symm
  exact (not_le_of_gt (ChapterD.janko_subspace_actor_ratio σ S hS eS U hU hfU _ hC)) hC.2.2

/-- Every original odd-prime row is impossible without moved minimality. -/
theorem original_odd_prime_excluded
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p)
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,ZMod p)) : False := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_odd_prime D c hp e ht htn
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let S := movedStabilizerComponentImage D
  let eS := (originalMovedComponentEquiv D c.nonnormal).trans e
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : IsSimpleGroup S := (originalMovedComponentEquiv D c.nonnormal).isSimpleGroup
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv (originalMovedComponentEquiv D c.nonnormal).symm
  let : IsQuasisimple PSL(2,ZMod p) := IsQuasisimple.of_mulEquiv e
  have hi : σ.IsIrreducible := imageRepresentation_isIrreducible ρ
    (movedStabilizerAction_irreducible D c ht htn hsep)
  have hsmall := movedStabilizerAction_cubic_bound D c ht htn hsep
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff σ).mpr hsmall
  have h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L) :=
    Theory.PSL2.prime_model_three_dvd_card (Fact.out : p.Prime)
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (by simp) e
  obtain ⟨hr,hm⟩ := original_starred_rank_and_movement D c ht htn hsep h3 A hA
  have hr2 : rank A ≤ 2 := by
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    exact hr.trans (Theory.PSL2.primeField_automorphism_two_rank (by omega : 3 < p))
  obtain ⟨U,hU,hfU⟩ := exists_faithful_normal_simple_constituent σ
    (imageRepresentation_injective ρ) hi S
  have hd : 5 ≤ Module.finrank (ZMod 2) U.toSubmodule := by
    have hh := SL2.odd_prime_faithful_degree (by omega : 3 < p)
      (U.toRepresentation.comp eS.symm.toMonoidHom) (hfU.comp eS.symm.injective)
    omega
  have hC := invariant_constituent_qhat_of_degree σ (imageRepresentation_injective ρ) hi
    S A hA hsmall hm U hU (by omega)
  have hS := (original_component_quotient_sqtk D).knownSimple_of_equiv
    (originalMovedComponentEquiv D c.nonnormal).symm
  exact (not_le_of_gt (ChapterD.odd_prime_subspace_actor_ratio hp σ S hS eS U hU hfU _ hC)) hC.2.2

/-- The source non-A5 and non-SL3 hypotheses remove the small odd-prime endpoints. -/
theorem original_odd_model_excluded
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p) : False := by
  have hlarge := original_odd_prime_parameter_large D c hnot hp ho hm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp (by
    simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact original_odd_prime_excluded D c hlarge (e.trans (Atlas.fieldEquivPSL 2 eF))

/-- The literal Hall exponent in the Janko branch, with its module premises discharged. -/
theorem hall_exponent_of_janko
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* Janko1.Model) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2^n+1 :=
  (original_janko_excluded D c e).elim

/-- The literal Hall exponent in every odd-prime branch, with its module premises discharged. -/
theorem hall_exponent_of_odd_model
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2^n+1 :=
  (original_odd_model_excluded D c hnot hp ho hm).elim

/-- The genuine nonlinear catalogue leaves only even-linear and Suzuki quotients. -/
theorem original_nonlinear_even_or_suzuki
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))) :
    (∃ n : ℕ, 3 ≤ n ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))) ∨
      ∃ m : ℕ, 0 < m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  cases component_model D c.nonnormal with
  | linear_even n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    let f : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
      simpa only [Fintype.card_eq_nat_card] using hF.trans (GaloisField.card 2 n (by omega)).symm)
    let a := (e.trans (Atlas.fieldEquivPSL 2 f)).trans (Theory.PSL2.sl2QuotientEquiv _).symm
    exact Or.inl ⟨n,original_even_parameter_ge_three D c hn a,⟨a⟩⟩
  | linear_prime p hp ho hm => exact (original_odd_model_excluded D c hnot hp ho hm).elim
  | janko he => exact (original_janko_excluded D c he.some).elim
  | suzuki m hm he => exact Or.inr ⟨m,by omega,he⟩

/-- The literal Hall consumer retains only the nonseparated even-linear seed
and the Suzuki row. Both component restrictions and the exact quotient kernel
remain in OriginalEvenNaturalAnalysis; no moved-minimality premise is added. -/
theorem hall_exponent_or_original_even_analysis_or_suzuki
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))) :
    (∃ r : ℕ, 1 < r ∧ Monoid.exponent B ∣ 2^r+1) ∨
      (∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
          ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
            D.seed ≤ centralizer (L : Set G)) ∧ OriginalEvenNaturalAnalysis D ht n e) ∨
      ∃ m : ℕ, 0 < m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rcases original_nonlinear_even_or_suzuki D c hnot with ⟨n,hn,⟨e⟩⟩ | hs
  · obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
    by_cases hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
        D.seed ≤ centralizer (L : Set G)
    · exact Or.inl (hall_exponent_of_even_linear_and_seed_separated D c hnot ht htn hsep
        n (by omega) e)
    · exact Or.inr (Or.inl ⟨t,ht,htn,n,hn,e,hsep,
        original_even_seed_constituent_or_natural D c n hn e ht htn hsep⟩)
  · exact Or.inr (Or.inr hs)
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules

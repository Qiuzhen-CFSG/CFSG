module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsOuter
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsNoncubicUnitary
public import Theory.GroupTheory.CComponent.FullRankOuterAction
public import Theory.GroupAction.PrimeCoefficientRepresentative
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage
public import Theory.FieldTheory.OddQuadraticCoefficientLift
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.Coefficients
public import Theory.SpecificGroups.ReeF4.PrimeFieldRepresentative
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank.Divisibility

/-!
This source variant uses the corrected record. Outer prime actors come from
full prime rank and root faithfulness, never from radical torus movement.

# Literal outer and field actors in the nonblock quotient sieve

Full prime rank makes each outside prime-order torus element outer on the
full component two-core quotient and bounds the rank of the actual action
image. On the remaining triality and Ree markings, coefficient separation
then forces the source prime to divide the field degree. The triality
witness also retains the original actor and a coefficient element inside
its transported action image.

For cubic linear markings, the same image-rank bound excludes field actors,
so the source torus acts by diagonal outer automorphisms. At the two
exceptional models, cubic rank two and the torus order give the required
trivial intersection with inner automorphisms on the original action.

These results reduce, but do not replace, the remaining source model
inspection: the fixed-field rank exclusions, unitary diagonal action and
four-row classification still have to be proved. In particular, the model
alternatives in the last assembly helper remain an explicit premise.
Source: Aschbacher–Smith A.3.18, printed pp.51–53, and 4.3.12(2),
4.3.14–16, printed pp.617–619.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

omit [Finite G] in
private theorem model_action_inner_le (s : SecondaryActionData c n)
    {M : Type*} [Group M] (e : (s.component ⧸ pCore 2 s.component) ≃* M) :
    MulAut.innerSubgroup M ≤ ((MulAut.congr e).toMonoidHom.comp s.action).range := by
  rw [MonoidHom.range_comp,←MulAut.map_innerSubgroup_congr e]
  apply map_mono
  rw [←SecondaryActionData.componentImage_eq_inner s]
  exact map_le_range _ _

private theorem model_action_rank (s : SecondaryActionData c n) {M : Type*} [Group M]
    (e : (s.component ⧸ pCore 2 s.component) ≃* M) {p : ℕ}
    (hr : primeRank p s.action.range ≤ 2) :
    primeRank p ((MulAut.congr e).toMonoidHom.comp s.action).range ≤ 2 := by
  let : Finite M := Finite.of_surjective e e.surjective
  rw [MonoidHom.range_comp,←primeRank_congr p
    (s.action.range.equivMapOfInjective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective)]
  exact hr

/-- The full original action retains an outer prime actor and the rank bound under any model marking. -/
theorem SecondaryActionData.model_prime_actor_of_rank_two (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hr : 2 ≤ primeRank p s.component) {M : Type*} [Group M]
    (e : (s.component ⧸ pCore 2 s.component) ≃* M) :
    ∃ x : rootNormalizer c, (x : G)∈s.torus ∧ orderOf x=p ∧
      orderOf (MulAut.congr e (s.action x))=p ∧
      MulAut.congr e (s.action x) ∉ MulAut.innerSubgroup M ∧
      MulAut.innerSubgroup M ≤ ((MulAut.congr e).toMonoidHom.comp s.action).range ∧
      primeRank p ((MulAut.congr e).toMonoidHom.comp s.action).range ≤ 2 := by
  obtain ⟨x,hxt,hx,ha,hi⟩ := SecondaryActionData.exists_outer_prime_torus_actor_of_rank_two s D h hp ho hd hr
  refine ⟨x,hxt,hx,(MulAut.congr e).orderOf_eq _ |>.trans ha,?_,
    model_action_inner_le s e,model_action_rank s e
      (SecondaryActionData.action_rank_le_two_of_component_rank_two s D h hp ho hd hr)⟩
  rintro ⟨g,hg⟩
  obtain ⟨b,hb⟩ := (MulAut.congr_inner_iff e (s.action x)).mp ⟨g,hg.symm⟩
  exact hi ⟨b,hb.symm⟩

private theorem simple_model_of_center_bot {B M : Type*} [Group B] [Group M]
    [IsQuasisimple B] (hz : center B=⊥) (e : B≃*M) : IsSimpleGroup M := by
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : IsSimpleGroup B := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  exact e.isSimpleGroup_congr.mp inferInstance

/-- The remaining triality row contains a literal prime-order coefficient actor;
its prime divides the base degree, not only the cubic extension degree. -/
theorem SecondaryActionData.noncubic_triality_field_actor (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1) (hp3 : p≠3)
    (hr : 2 ≤ primeRank p s.component) (hf : 0<f)
    (e : (s.component ⧸ pCore 2 s.component) ≃* Triality.Standard.BinaryCarrier f hf) :
    p ∣ f ∧
    ∃ x : rootNormalizer c, (x : G) ∈ s.torus ∧ orderOf x=p ∧
      ∃ (g : Triality.Standard.BinaryCarrier f hf)
        (σ : Triality.Standard.OuterOdd.CoefficientAut (Triality.Standard.binaryParameters f hf)),
        MulAut.congr e (s.action x) = MulAut.conj g *
          Triality.Standard.OuterOdd.coefficientAction _ σ ∧ orderOf σ=p ∧
        Triality.Standard.OuterOdd.coefficientAction _ σ ∈
          ((MulAut.congr e).toMonoidHom.comp s.action).range ∧
        orderOf (Triality.Standard.OuterOdd.coefficientAction _ σ)=p ∧
        Triality.Standard.OuterOdd.coefficientAction _ σ ∉
          MulAut.innerSubgroup (Triality.Standard.BinaryCarrier f hf) ∧
        primeRank p ((MulAut.congr e).toMonoidHom.comp s.action).range ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hxt,hx,ha,hi⟩ := SecondaryActionData.exists_outer_prime_torus_actor_of_rank_two s D h hp ho hd hr
  let := s.quasisimple
  let : IsQuasisimple (Triality.Standard.BinaryCarrier f hf) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (Triality.Standard.BinaryCarrier f hf) := by
    let : IsSimpleGroup (Triality.Standard.BinaryCarrier f hf ⧸
      center (Triality.Standard.BinaryCarrier f hf)) := IsQuasisimple.simple
    exact ((QuotientGroup.quotientMulEquivOfEq
      (Triality.Standard.binaryCarrier_center_eq_bot f hf)).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  let P := Triality.Standard.binaryParameters f hf
  let φ := Triality.Standard.OuterOdd.coefficientAction P
  have hfaithful : Function.Injective ((QuotientGroup.mk' (MulAut.innerSubgroup
      (Triality.Standard.BinaryCarrier f hf))).comp φ) := by
    apply (injective_iff_map_eq_one _).mpr
    intro σ hσ
    exact (Triality.Standard.EvenField.NormalForm.coefficientAction_mem_inner_iff f hf σ).mp
      ((QuotientGroup.eq_one_iff _).mp hσ)
  have hin : MulAut.congr e (s.action x) ∉ MulAut.innerSubgroup _ := by
    rintro ⟨g,hg⟩
    obtain ⟨b,hb⟩ := (MulAut.congr_inner_iff e (s.action x)).mp ⟨g,hg.symm⟩
    exact hi ⟨b,hb.symm⟩
  obtain ⟨g,σ,he,hσ,hσA,hoσ,hnσ⟩ := MulAut.exists_prime_coefficient_in_overgroup φ hfaithful
    (Triality.Standard.OuterOdd.Coverage.binary_inner_coefficient f hf)
    _ (model_action_inner_le s e) _ ⟨x,rfl⟩
    ((MulAut.congr e).orderOf_eq _ |>.trans ha) hin
  have hc : Nat.card (Triality.Standard.OuterOdd.CoefficientAut P)=3*f :=
    GaloisField.card_ringAut 2 (3*f) (by omega)
  have hdiv : p ∣ f := (hp.dvd_mul.mp (hc ▸ (hσ ▸ orderOf_dvd_natCard σ))).resolve_left
    (by intro hh; exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hh))
  exact ⟨hdiv,x,hxt,hx,g,σ,he,hσ,hσA,hoσ,hnσ,model_action_rank s e
    (SecondaryActionData.action_rank_le_two_of_component_rank_two s D h hp ho hd hr)⟩

/-- On the actual Ree marking, the outside source torus forces its prime to divide
 the degree of the canonical field automorphism. -/
theorem SecondaryActionData.ree_field_degree_divisibility (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p m : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hr : 2 ≤ primeRank p s.component) (hm : 1≤m)
    (hz : center (s.component ⧸ pCore 2 s.component)=⊥)
    (d : ReeF4.LocalBlockInput m)
    (e : (s.component ⧸ pCore 2 s.component) ≃* d.fixedGroup) : p ∣ 2*m+1 := by
  let : Fact p.Prime := ⟨hp⟩
  let := s.quasisimple
  let : IsSimpleGroup d.fixedGroup := simple_model_of_center_bot hz e
  let : Group.IsPerfect d.fixedGroup := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨x,hxt,hx,ha,hi,hinner,hbound⟩ := SecondaryActionData.model_prime_actor_of_rank_two s D h hp ho hd hr e
  exact (ReeF4.LocalBlockInput.exists_prime_field_representative hm d _ hinner _ ⟨x,rfl⟩ ha hi).1

/-- Every remaining noncubic rank-two row has a field degree divisible by the
source prime. Coprime degrees, including the binary triality endpoint, are excluded. -/
theorem SecondaryActionData.noncubic_rank_two_field_divisibility (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1) (hp3 : p≠3)
    (hr : 2 ≤ primeRank p s.component) :
    center (s.component ⧸ pCore 2 s.component)=⊥ ∧
      ((∃ f : ℕ, 1≤f ∧ p ∣ f ∧ Triality.Standard.IsTrialityGroupAt (2^f)
        (s.component ⧸ pCore 2 s.component)) ∨
       (∃ m : ℕ, 1≤m ∧ p ∣ 2*m+1 ∧ IsReeF4At (s.component ⧸ pCore 2 s.component) m)) := by
  obtain ⟨hz,hm⟩ := SecondaryActionData.noncubic_rank_two_triality_or_ree s D h hp ho hd hp3 hr
  refine ⟨hz,?_⟩
  rcases hm with ⟨f,hf,he⟩ | ⟨m,hm,he⟩
  · obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f (by omega)).mp he
    exact Or.inl ⟨f,hf,(SecondaryActionData.noncubic_triality_field_actor s D h hp ho hd hp3 hr
      (by omega) e).1,he⟩
  · obtain ⟨d,⟨e⟩⟩ := he
    exact Or.inr ⟨m,hm,SecondaryActionData.ree_field_degree_divisibility s D h hp ho hd hr hm hz d e,d,⟨e⟩⟩
open scoped MatrixGroups

/-- On every binary linear marking the original cubic torus actor is diagonal outer.
The field component is excluded using the rank of the full actual action image. -/
theorem SecondaryActionData.binary_linear_cubic_torus_diagonal (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2^n-1) (hr : 2 ≤ primeRank 3 s.component)
    {F : Type*} [Field F] [Finite F] {f : ℕ} (hf : 0<f) (hF : Nat.card F=2^f)
    (e : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F))
    (x : rootNormalizer c) (hxt : (x : G) ∈ s.torus) (hx : orderOf x=3) :
    MulAut.congr e (s.action x) ∈ Matrix.PSL3.OuterSolvable.innerDiagonal F ∧
      MulAut.congr e (s.action x) ∉ MulAut.innerSubgroup PSL(3,F) := by
  let := s.quasisimple
  have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h hd
  let : IsSimpleGroup (s.component ⧸ pCore 2 s.component) := by
    let : IsSimpleGroup ((s.component ⧸ pCore 2 s.component) ⧸ center
      (s.component ⧸ pCore 2 s.component)) := IsQuasisimple.simple
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  let : IsSimpleGroup PSL(3,F) := e.isSimpleGroup_congr.mp inferInstance
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let a := MulAut.congr e (s.action x)
  have hi : a ∉ MulAut.innerSubgroup PSL(3,F) := by
    rw [←MulAut.map_innerSubgroup_congr e]
    rintro ⟨b,hb,he⟩
    exact SecondaryActionData.torus_prime_action_not_inner_of_rank_two s D h Nat.prime_three
      (by decide) hd hr x hxt hx ((MulAut.congr e).injective he ▸ hb)
  have ha : orderOf a=3 := by
    apply orderOf_eq_prime
    · change MulAut.congr e (s.action x)^3=1
      rw [←map_pow,←map_pow,show x^3=1 from hx ▸ pow_orderOf_eq_one x,map_one,map_one]
    · exact fun he => hi (he ▸ (MulAut.innerSubgroup _).one_mem)
  have heven : Even f := by
    apply Matrix.PSL3.BinaryCubicRankParity.even_of_rank_two hF
    rw [←primeRank_congr 3 e,primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact hr
  let A := ((MulAut.congr e).toMonoidHom.comp s.action).range
  have hinner : MulAut.innerSubgroup PSL(3,F) ≤ A := model_action_inner_le s e
  have hrA : primeRank 3 A ≤ 2 := model_action_rank s e
    (SecondaryActionData.action_rank_le_two_of_component_rank_two s D h Nat.prime_three
      (by decide) hd hr)
  refine ⟨?_,hi⟩
  apply Matrix.PSL3.StandardCubicFixedNine.innerDiagonal_of_primeRank_three_le_two
    (Group.IsPerfect.not_isSolvable PSL(3,F)) hF heven A hinner hrA a ⟨x,rfl⟩ _ ha
  rw [Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F hf hF]
  trivial

/-- Prime-field linear cubic actors are also diagonal on the original marked quotient. -/
theorem SecondaryActionData.odd_linear_cubic_torus_diagonal (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2^n-1) (hr : 2 ≤ primeRank 3 s.component)
    {F : Type*} [Field F] [Finite F] {r : ℕ}
    (hrp : r.Prime) (hro : Odd r) (hF : Nat.card F=r)
    (e : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F))
    (x : rootNormalizer c) (hxt : (x : G) ∈ s.torus) (hx : orderOf x=3) :
    MulAut.congr e (s.action x) ∈ Matrix.PSL3.OuterSolvable.innerDiagonal F ∧
      MulAut.congr e (s.action x) ∉ MulAut.innerSubgroup PSL(3,F) := by
  let := s.quasisimple
  have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h hd
  let : IsSimpleGroup (s.component ⧸ pCore 2 s.component) := by
    let : IsSimpleGroup ((s.component ⧸ pCore 2 s.component) ⧸ center
      (s.component ⧸ pCore 2 s.component)) := IsQuasisimple.simple
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  let : IsSimpleGroup PSL(3,F) := e.isSimpleGroup_congr.mp inferInstance
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let a := MulAut.congr e (s.action x)
  have hi : a ∉ MulAut.innerSubgroup PSL(3,F) := by
    rintro ⟨g,hg⟩
    obtain ⟨b,hb⟩ := (MulAut.congr_inner_iff e (s.action x)).mp ⟨g,hg.symm⟩
    exact SecondaryActionData.torus_prime_action_not_inner_of_rank_two s D h Nat.prime_three
      (by decide) hd hr x hxt hx ⟨b,hb.symm⟩
  have ha3 : a^3=1 := by
    change MulAut.congr e (s.action x)^3=1
    rw [←map_pow,←map_pow,show x^3=1 from hx ▸ pow_orderOf_eq_one x,map_one,map_one]
  have ha2 := Matrix.PSL3.OuterSolvable.OddPrimeSquares.square_mem_innerDiagonal
    (Group.IsPerfect.not_isSolvable PSL(3,F)) hrp hro hF a
  have he : (a^2)^2=a := by
    rw [←pow_mul,show 2*2=3+1 from rfl,pow_succ,ha3,one_mul]
  refine ⟨?_,hi⟩
  change a ∈ Matrix.PSL3.OuterSolvable.innerDiagonal F
  rw [←he]
  exact (Matrix.PSL3.OuterSolvable.innerDiagonal F).pow_mem ha2 2
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ExceptionalQuadratic
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.TrialityCyclotomic

/-!
# Removing the remaining triality rows from normal split-prime A.3.18

The cyclotomic fixed-plane construction excludes the third and sixth
cyclotomic triality primes under the actual SQTK bound. Transport through
the original central model and literal two-core quotient preserves the
outside actor. Together with the existing quadratic exclusion this removes
the triality row entirely. Nonsplit Ree actors and outer central cubic
covers remain explicit obligations. The ordinary-root leaf applies this
to its actual Cartan extension, with no additional fixed-point premise.

Source: Aschbacher–Smith A.3.18, pp.51–53, and 4.3.6, p.615.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
open Triality.Standard Triality.Standard.OuterOdd
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

variable {H : Type*} [Group H] [Finite H]

/-- Exclude the ordinary triality row at a cyclotomic prime using the
actual outside actor and inherited SQTK rank bound. -/
theorem ordinary_not_triality_cyclotomic_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hr : 1 < primeRank p K) (hz : Nat.Coprime p (Nat.card (center K)))
    {n : ℕ} (hn : 1 ≤ n) (hpgt : 3 < p)
    (hd : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 ∨ p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) (K ⧸ center K))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := hn
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n hn0).mp hmodel
  let : IsSimpleGroup (Triality.Standard.BinaryCarrier n hn0) :=
    e.isSimpleGroup_congr.mp IsQuasisimple.simple
  let : Group.IsPerfect (Triality.Standard.BinaryCarrier n hn0) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let f := normalAction K e
  have hb := hH.stronglyQuasithin p hp ho
  apply outside_action_not_inner hz hr hb e a ha haK
  apply TrialityCyclotomic.prime_actor_inner n hn0 hpgt hd f.range
    (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
    (normalAction_rank_le_two hz hr hb e) (f a) ⟨a, rfl⟩
  rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]

/-- Transport the triality cyclotomic-prime exclusion to the literal two-core
component, preserving the actual quotient image of the outside actor. -/
theorem not_triality_cyclotomic_twoCore_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    {n : ℕ} (hn : 1 ≤ n) (hpgt : 3 < p)
    (hd : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 ∨ p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hz' : Nat.Coprime p (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 1 < primeRank p (twoCoreComponent K) := by rwa [twoCore_rank hK ho]
  have ha' := twoCore_actor hp ho a ha haK
  exact ordinary_not_triality_cyclotomic_model (twoCore_sqtk hH) hp ho hr' hz' hn hpgt hd
    (hmodel.of_mulEquiv (centralQuotientEquiv (twoCoreComponentEquiv hK)))
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2
open Chapter1.Section02.LocalModels

/-- After the fixed-subfield triality argument, only the nonsplit Ree and
outer central cubic-cover branches remain. The original actor is retained. -/
def ReeOrCoverRemainder (p : ℕ) (K : Subgroup H) (a : H) : Prop :=
  (p ≠ 3 ∧ Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) ∧
    ∃ m : ℕ, 1 ≤ m ∧ ¬ p ∣ 2^(2*m+1)-1 ∧
      IsReeF4At ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) m) ∨
  (p = 3 ∧ OuterCubicCoverActor (twoCoreComponent K) (QuotientGroup.mk' (pCore 2 H) a))

/-- Exclude the last triality cyclotomic primes on the actual split extension,
using an elementary square fixed by its marked coefficient representative. -/
theorem alternatives_or_ree_or_cover
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ ReeOrCoverRemainder p K a := by
  rcases alternatives_or_refined_nonsplit_or_cover hH hK hp ho hr a ha haK hgen with halt | hrem
  · exact Or.inl halt
  rcases hrem with ⟨hp3, hz, hm⟩ | hcover
  · rcases hm with ⟨n, hn, _, _, hd, hm⟩ | hree
    · have hpgt : 3 < p := by
        have := hp.two_le
        have := Nat.odd_iff.mp ho
        omega
      exact (not_triality_cyclotomic_twoCore_model hH hK hp ho hr hz hn hpgt hd hm a ha haK).elim
    · exact Or.inr (Or.inl ⟨hp3, hz, hree⟩)
  · exact Or.inr (Or.inr hcover)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

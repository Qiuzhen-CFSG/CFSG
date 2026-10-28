module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ActionBounds
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Binary
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Cubic
public import Theory.SpecificGroups.G2.CubicFieldActors
public import Theory.SpecificGroups.Triality.CubicComponentAction
public import Theory.SpecificGroups.ReeF4.CubicFieldActors

/-!
# Four cubic field-actor exclusions on the original split domain

The symplectic, G₂, triality and Ree models have actual elementary nine-groups
fixed by their pure cubic field actors. Their inner images together with an
outside cubic force rank three. The proved model coverage and field extraction
therefore make every cubic in the rank-two action image inner. Applying this
to the original outside element contradicts its outer order three.

The source application passes through H/O₂(H), retaining the component's
central quotient and p-prime center. It needs no assumption that the whole
component rank is attained by a field fixed group: the imported fixed-nine
constructions supply the necessary witnesses. Source: Aschbacher–Smith
A.3.18, printed pp.51–53, using the GLS3 automorphism and fixed-group formulas.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Chapter1.Section02.LocalModels

/-- The four characteristic-two rows whose cubic field actors are excluded by
fixed elementary nine-groups. Every predicate includes the actual model map. -/
inductive CubicFieldModel (S : Type*) [Group S] : Prop
  | symplectic (n : ℕ) (hn : 2 ≤ n) (model : ClassicalGroup.IsPSp S 2 (2 ^ n))
  | g2 (n : ℕ) (hn : 2 ≤ n) (model : ClassificationModels.IsG2At S (2 ^ n))
  | triality (n : ℕ) (hn : 1 ≤ n) (model : Triality.Standard.IsTrialityGroupAt (2 ^ n) S)
  | ree (m : ℕ) (hm : 1 ≤ m) (model : IsReeF4At S m)

theorem CubicFieldModel.of_mulEquiv {S T : Type*} [Group S] [Group T]
    (hm : CubicFieldModel S) (e : T ≃* S) : CubicFieldModel T := by
  cases hm with
  | symplectic n hn hm => exact .symplectic n hn (hm.of_mulEquiv e)
  | g2 n hn hm => exact .g2 n hn (hm.of_mulEquiv e)
  | triality n hn hm => exact .triality n hn (hm.of_mulEquiv e)
  | ree m hm hmodel =>
    obtain ⟨d, ⟨a⟩⟩ := hmodel
    exact .ree m hm ⟨d, ⟨e.trans a⟩⟩

variable {H : Type*} [Group H] [Finite H]

theorem ordinary_not_cubic_field_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    (hr : 1 < primeRank 3 K) (hz : Nat.Coprime 3 (Nat.card (center K)))
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) :
    ¬ CubicFieldModel (K ⧸ center K) := by
  intro hm
  have hb := hH.stronglyQuasithin 3 Nat.prime_three (by decide)
  have hapow : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  cases hm with
  | symplectic n hn hm =>
    obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
      omega
    let e := e₀.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
    let f := normalAction K e
    apply outside_action_not_inner hz hr hb e a ha haK
    apply Theory.SpecificGroups.SymplecticFour.OddFieldActors.cubic_primePower_actor_inner hlarge f.range
      (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
      (normalAction_rank_le_two hz hr hb e) (f a) ⟨a, rfl⟩
    exact ⟨1, by rw [pow_one, ← map_pow, hapow, map_one]⟩
  | g2 n hn hm =>
    obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
      omega
    let e := e₀
    let f := normalAction K e
    apply outside_action_not_inner hz hr hb e a ha haK
    apply Atlas.G2.CubicFieldActors.cubic_primePower_actor_inner hlarge f.range
      (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
      (normalAction_rank_le_two hz hr hb e) (f a) ⟨a, rfl⟩
    exact ⟨1, by rw [pow_one, ← map_pow, hapow, map_one]⟩
  | triality n hn hm =>
    have hn0 : 0 < n := by omega
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n hn0).mp hm
    let : IsSimpleGroup (Triality.Standard.BinaryCarrier n hn0) :=
      e.isSimpleGroup_congr.mp IsQuasisimple.simple
    let : Group.IsPerfect (Triality.Standard.BinaryCarrier n hn0) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let f := normalAction K e
    apply outside_action_not_inner hz hr hb e a ha haK
    apply Triality.Standard.CubicComponentAction.primePower_actor_inner n hn0 f.range
      (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
      (normalAction_rank_le_two hz hr hb e) (f a) ⟨a, rfl⟩
      1
    rw [pow_one, ← map_pow, hapow, map_one]
  | ree m hm hmodel =>
    obtain ⟨d, ⟨e₀⟩⟩ := hmodel
    let e := e₀.trans d.modelEquiv
    let : IsSimpleGroup (ReeF4.Model m) := e.isSimpleGroup_congr.mp IsQuasisimple.simple
    let : Group.IsPerfect (ReeF4.Model m) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let f := normalAction K e
    apply outside_action_not_inner hz hr hb e a ha haK
    apply ReeF4.CubicFieldActors.cubic_primePower_actor_inner hm f.range
      (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
      (normalAction_rank_le_two hz hr hb e) (f a) ⟨a, rfl⟩
    exact ⟨1, by rw [pow_one, ← map_pow, hapow, map_one]⟩

/-- Apply the fixed-subfield exclusions after the literal two-core reduction. -/
theorem not_cubic_field_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : 1 < primeRank 3 K)
    (hz : Nat.Coprime 3 (Nat.card (center (K ⧸ pCore 2 K))))
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) :
    ¬ CubicFieldModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) := by
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hz' : Nat.Coprime 3 (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 1 < primeRank 3 (twoCoreComponent K) := by
    rwa [twoCore_rank hK (by decide : Odd 3)]
  have ha' := twoCore_actor Nat.prime_three (by decide) a ha haK
  intro hm
  exact ordinary_not_cubic_field_model (twoCore_sqtk hH) hr' hz'
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2
    (hm.of_mulEquiv (centralQuotientEquiv (twoCoreComponentEquiv hK)))

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

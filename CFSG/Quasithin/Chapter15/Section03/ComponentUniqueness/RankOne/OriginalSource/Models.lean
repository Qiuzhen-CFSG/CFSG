module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.OriginalSource.Complete
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.Complete
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OddModels.LinearTwo
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OddModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OddModels.AlternatingSeven
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OddModels.SmallParameters
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115.Transport
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure

/-!
# The full marked component contradiction for the original reduction

Every constructor of the actual marked 1.1.5 model list is dispatched to
its original source exclusion. The central involution retains its literal
conjugation action, and the small odd linear parameters are transported to
the already excluded binary models. No stronger centralizer premise is used.

Source: Aschbacher--Smith 1.1.5 and 15.3.43, pp.501--503,1139--1140.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne
open Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {Y S M I L V₁ V₂ : Subgroup G}

omit [Finite G] in
private theorem inner_of_mark {α : MulAut L} {z : G}
    (ha : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := L)).range) : EvenModels.ActsInner L z := by
  obtain ⟨l, hl⟩ := hi
  refine ⟨l, fun x => ?_⟩
  exact (ha x).symm.trans (congrArg Subtype.val (DFunLike.congr_fun hl.symm x))

private theorem fermat_mersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hh : 2 ≤ 2 ^ (2 ^ k) := Nat.le_pow (by positivity)
    omega
  · have hk0 : k ≠ 0 := by intro he; simp [he] at hk
    have hh := dvd_pow_self 2 hk0
    rw [← hk] at hh
    norm_num at hh

/-- Every marked1.1.5 alternative contradicts the original reduced
configuration. The source involution is kept on the original component. -/
theorem not_modelAction115_of_original_configuration
    (c : ReducedConfiguration Y S M I L V₁ V₂)
    {α : MulAut L} {z : G}
    (ha : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hm : ModelAction115 L α) : False := by
  let : IsQuasisimple (L.subgroupOf I) := c.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe c.component_le)
  have hthree : 3 ∣ Nat.card L :=
    (c.index ▸ (pCore 2 Y).index_dvd_card).trans (card_dvd_of_le c.y_le_component)
  have halt (n : ℕ) {σ : Equiv.Perm (Fin n)} (h : AlternatingAction α n σ) :
      Nonempty (L ≃* alternatingGroup (Fin n)) := by
    rcases h with ⟨e, _⟩ | ⟨_, ⟨e⟩, _⟩
    · exact ⟨e⟩
    · have hc : Nat.card (center L) = 3 := by
        rw [Nat.card_congr e.toEquiv]
        simp [Nat.card_eq_fintype_card]
      exact ((EvenModels.center_card_ne_three c) hc).elim
  cases hm with
  | lie hs hm hi =>
    have hn (n : ℕ) (h : EvenModels.SimpleModel L n) : False :=
      EvenModels.not_model_of_original_configuration c (.simple hs h (inner_of_mark ha hi))
    rcases hm with hb | ht | ⟨n, hn', hm⟩
    · cases hb with
      | linear f hf he => exact hn f (.linearTwo hf he)
      | unitary f hf he => exact hn f (.unitaryThree hf he)
      | suzuki m hm he =>
        obtain ⟨e⟩ := he
        rw [Nat.card_congr e.toEquiv] at hthree
        exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hthree
    · cases ht with
      | linear f hf he => exact hn f (.rankTwo (.linear hf he))
      | symplectic f hf he => exact hn f (.rankTwo (.symplectic hf he))
      | g2 f hf he => exact hn f (.rankTwo (.g2 hf he))
      | triality f hf he => exact hn f (.rankTwo (.triality hf he))
      | ree m hm he =>
        obtain ⟨d, ⟨e⟩⟩ := he
        exact hn (2 * m + 1) (.rankTwo (.ree_f4 m hm rfl ⟨e.trans d.modelEquiv⟩))
      | symplectic_derived he => exact hn 1 (.rankTwo (.symplectic_derived rfl he))
      | g2_derived he => exact hn 1 (.rankTwo (.g2_derived rfl he))
      | tits he => exact hn 1 (.rankTwo (.tits rfl he))
    · exact hn 1 (.binaryLinear rfl n hn' hm)
  | two_cover hn hc hm hi =>
    rcases hm with hm | hm
    · exact EvenModels.not_model_of_original_configuration c
        (.linearThreeCover rfl hn
          (hm.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hc)) (inner_of_mark ha hi))
    · exact EvenModels.not_model_of_original_configuration c
        (.g2Cover rfl hn
          (hm.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hc)) (inner_of_mark ha hi))
  | six σ _ hm =>
    obtain ⟨e⟩ := halt 6 hm
    exact c.not_alternating_four (EvenModels.BinaryInspection.SixInspection.actor_alternating_four c ⟨e⟩)
  | seven σ _ hm =>
    obtain ⟨e⟩ := halt 7 hm
    exact OddModels.not_alternating_seven c e
  | odd hm hi =>
    rcases hm with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨p, hp, F, _, _, hF, ⟨e⟩⟩
    · let : Fintype F := Fintype.ofFinite F
      let f : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
      exact OddModels.not_linear_three c (e.trans (Atlas.fieldEquivPSL 3 f))
    · have hns : ¬ Group.IsSolvable PSL(2, F) := by
        intro hs
        let := hs
        let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
        let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
        exact Group.IsPerfect.not_isSolvable L
          (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
      have hlarge := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
        (hF ▸ fermat_mersenne_odd hp) hns
      let : IsSimpleGroup PSL(2, F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
      let : IsSimpleGroup L := e.isSimpleGroup
      by_cases hp7 : 7 < p
      · exact OddModels.not_linear_two_field c hp hp7 hF e
      have hsmall : p = 5 ∨ p = 7 := by
        have hprime := hp.1
        have hp4 : 3 < p := by omega
        interval_cases p <;> norm_num at *
      rcases hsmall with rfl | rfl
      · have he := OddModels.linear_two_five_transport hF e
        have hm : ClassicalGroup.IsPSL L 2 (2 ^ 2) :=
          ⟨GaloisField 2 2, inferInstance, inferInstance, GaloisField.card 2 2 (by decide), he⟩
        exact EvenModels.not_model_of_original_configuration c
          (.simple inferInstance (.linearTwo (by decide) hm) (inner_of_mark ha hi))
      · have he := OddModels.linear_two_seven_transport hF e
        have hm : ClassicalGroup.IsPSL L 3 (2 ^ 1) :=
          ⟨ZMod 2, inferInstance, inferInstance, by simp, he⟩
        exact EvenModels.not_model_of_original_configuration c
          (.simple inferInstance (.rankTwo (.linear (by decide) hm)) (inner_of_mark ha hi))
  | sporadic name hn hm _ =>
    exact SporadicModels.reduced_not_listed_two_core_quotient c ⟨name, hn, hm⟩

/-- Apply the full model inspection to the actual relative component and
its literal source conjugation, preserving the selected central involution. -/
theorem not_marked_component_of_original_configuration
    (c : ReducedConfiguration Y S M I L V₁ V₂) {z : G}
    (h33 : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) M z) : False := by
  obtain ⟨α, ha, hm⟩ := h33.model_action
  let e := subgroupOfEquivOfLe c.component_le
  have hmodel := hm.of_mulEquiv e.symm
  apply not_modelAction115_of_original_configuration c (z := z) ?_ hmodel
  intro x
  change ((α (e.symm x) : I) : G) = z * (x : G) * z⁻¹
  exact ha (e.symm x)

end CFSG.Quasithin.Chapter15.Section03.RankOne

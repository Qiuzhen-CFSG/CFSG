module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SporadicReduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsHigmanSims
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# Seven sporadic containing quotients in 10.2.6

A solvable representation kernel preserves the order of the original
simple quotient. If three does not divide that quotient, the source
nonnormal-component catalogue makes it a Suzuki group. The two-part of
each of the seven containing orders bounds the Suzuki parameter by four;
the four resulting orders fail divisibility in every case.

The five Mathieu carriers, Hall--Janko and Higman--Sims also have the
proved full-Sylow component uniqueness property. Thus both distinctness
and cubic divisibility follow for either strict original containing factor,
and the existing ranked-enlargement contradiction excludes the pair.
Combining the full Theorem C reduction leaves precisely J₄, Held or
Rudvalis as the quotient of an actual strict containing component.

The three remaining sporadic cases, the zero-kernel binary-three normalizer
and final assembly stay with qt-d-10-nona5-half-sylow-unique. In particular,
the order of Suzuki(8) divides the Rudvalis order, so that row requires
its local embedding information. ModuleChoiceAt is the independent input
of qt-d-10-nona5-point-selection; qt-d-10-nona5-point-control retains its
final discharge and the unconditional half-Sylow theorem.
Source: Aschbacher--Smith A.3.12 and 10.2.6, pp.47--48,748--749. The carrier
orders and local calculations retain the source attribution in their imports.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

private theorem suzuki_order_not_dvd_seven_orders {N : ℕ}
    (hN : N = 7920 ∨ N = 95040 ∨ N = 443520 ∨ N = 10200960 ∨
      N = 244823040 ∨ N = 604800 ∨ N = 44352000)
    {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∣ N := by
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m (by omega)]
  intro hd
  have h22 : ¬ 2 ^ 22 ∣ N := by
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hb : m ≤ 4 := by
    by_contra h
    apply h22
    have hp : (2 ^ (2*m+1)) ^ 2 ∣ N :=
      (dvd_mul_of_dvd_left (dvd_mul_left _ _) _).trans hd
    have he : 2 ^ 22 ∣ (2 ^ (2*m+1)) ^ 2 := by
      rw [←pow_mul]
      exact Nat.pow_dvd_pow 2 (by omega)
    exact he.trans hp
  interval_cases m <;>
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hd

/-- A solvable representation into a group without Suzuki sections forces a cubic. -/
theorem source_three_dvd_of_solvable_image_without_suzuki
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {X : Type*} [Group X] (r : L →* X) [Group.IsSolvable r.ker]
    (horder : ∀ m : ℕ, 1 ≤ m →
      ¬ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∣ Nat.card X) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  by_contra h3
  obtain ⟨m,hm,⟨e⟩⟩ :=
    (Selection.ModuleChoice.component_quotient_model D hn).suzuki_of_three_free h3
  apply horder m hm
  rw [←Nat.card_congr e.toEquiv]
  exact source_quotient_card_dvd_of_solvable_image D hn r

/-- The order test applies to the literal first two-core quotient. -/
theorem ContainingPair.three_dvd_of_first_quotient_without_suzuki
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (horder : ∀ m : ℕ, 1 ≤ m →
      ¬ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∣ Nat.card (K₁ ⧸ pCore 2 K₁)) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  let b := (subgroupOfEquivOfLe C.left_le).symm
  let j := (inclusion C.first_le).comp b.toMonoidHom
  let q := (QuotientGroup.mk' (pCore 2 K₁)).comp j
  have hk : q.ker = (pCore 2 K₁).comap j := by
    ext x
    exact QuotientGroup.eq_one_iff (j x)
  have hp : IsPGroup 2 q.ker := hk.symm ▸ pCore_isPGroup.comap_of_injective j
    ((inclusion_injective C.first_le).comp b.injective)
  let := hp.isNilpotent
  exact source_three_dvd_of_solvable_image_without_suzuki D hn q horder

/-- The second quotient uses the original exchanger in its source representation. -/
theorem ContainingPair.three_dvd_of_second_quotient_without_suzuki
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (horder : ∀ m : ℕ, 1 ≤ m →
      ¬ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∣ Nat.card (K₂ ⧸ pCore 2 K₂)) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  let b := C.rightEquiv
  let j := (inclusion C.second_le).comp b.toMonoidHom
  let q := (QuotientGroup.mk' (pCore 2 K₂)).comp j
  have hk : q.ker = (pCore 2 K₂).comap j := by
    ext x
    exact QuotientGroup.eq_one_iff (j x)
  have hp : IsPGroup 2 q.ker := hk.symm ▸ pCore_isPGroup.comap_of_injective j
    ((inclusion_injective C.second_le).comp b.injective)
  let := hp.isNilpotent
  exact source_three_dvd_of_solvable_image_without_suzuki D hn q horder

private theorem seven_sporadic_tests {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X] [Group.IsPerfect X] {name : SporadicName}
    (hj3 : name ≠ .j3) (hj4 : name ≠ .j4) (hhe : name ≠ .he) (hru : name ≠ .ru)
    (he : Nonempty (X ≃* name.Carrier)) :
    SylowOvergroupComponentUnique X ∧ (∀ m : ℕ, 1 ≤ m →
      ¬ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∣ Nat.card X) := by
  have ho : Nat.card X = 7920 ∨ Nat.card X = 95040 ∨ Nat.card X = 443520 ∨
      Nat.card X = 10200960 ∨ Nat.card X = 244823040 ∨ Nat.card X = 604800 ∨
      Nat.card X = 44352000 := by
    rw [Nat.card_congr he.some.toEquiv]
    cases name <;> try contradiction
    all_goals dsimp only [SporadicName.Carrier]
    · rw [Sporadic.Mathieu.m11_order]
      norm_num
    · rw [Sporadic.Mathieu.m12_order]
      norm_num
    · rw [Sporadic.Mathieu.m22_order]
      norm_num
    · rw [Sporadic.Mathieu.m23_order]
      norm_num
    · rw [Sporadic.Mathieu.m24_order]
      norm_num
    · rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
      norm_num
    · rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
      norm_num
  refine ⟨?_,fun _ hm => suzuki_order_not_dvd_seven_orders ho hm⟩
  cases name <;> try contradiction
  · exact Section02.MovedMaximality.mathieu_eleven_sylow_overgroup_component_unique he
  · exact Section02.MovedMaximality.mathieu_twelve_sylow_overgroup_component_unique he
  · exact Section02.MovedMaximality.mathieu_twenty_two_sylow_overgroup_component_unique he
  · exact Section02.MovedMaximality.mathieu_twenty_three_sylow_overgroup_component_unique he
  · exact Section02.MovedMaximality.mathieu_twenty_four_sylow_overgroup_component_unique he
  · exact Section02.MovedMaximality.janko_two_sylow_overgroup_component_unique he
  · exact Section02.MovedMaximality.higman_sims_sylow_overgroup_component_unique he

/-- Seven sporadic first quotients discharge both distinctness and cubic divisibility. -/
theorem ContainingPair.impossible_of_first_strict_seven_sporadic_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : L.subgroupOf H < K₁)
    {name : SporadicName} (hj3 : name ≠ .j3) (hj4 : name ≠ .j4)
    (hhe : name ≠ .he) (hru : name ≠ .ru)
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* name.Carrier)) : False := by
  let := C.first_quasisimple_of_strict hchoice hmany hn hna hstrict
  let := C.component_coreQuotient_simple hchoice hmany hn hna K₁ C.first_component
  obtain ⟨hu,ho⟩ := seven_sporadic_tests hj3 hj4 hhe hru he
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_first_sylow_unique_quotient (MulEquiv.refl _) hu)
    (C.three_dvd_of_first_quotient_without_suzuki hn ho)

/-- The same seven exclusions retain the original second factor. -/
theorem ContainingPair.impossible_of_second_strict_seven_sporadic_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : (L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂)
    {name : SporadicName} (hj3 : name ≠ .j3) (hj4 : name ≠ .j4)
    (hhe : name ≠ .he) (hru : name ≠ .ru)
    (he : Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* name.Carrier)) : False := by
  let := C.second_quasisimple_of_strict hchoice hmany hn hna hstrict
  let := C.component_coreQuotient_simple hchoice hmany hn hna K₂ C.second_component
  obtain ⟨hu,ho⟩ := seven_sporadic_tests hj3 hj4 hhe hru he
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_second_sylow_unique_quotient (MulEquiv.refl _) hu)
    (C.three_dvd_of_second_quotient_without_suzuki hn ho)

/-- The actual strict containing factor is now restricted to J₄, Held or Rudvalis. -/
theorem ContainingPair.exists_strict_large_sporadic_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    ∃ name : SporadicName, (name = .j4 ∨ name = .he ∨ name = .ru) ∧
      ((L.subgroupOf H < K₁ ∧ Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* name.Carrier)) ∨
       ((L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂ ∧
         Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* name.Carrier))) := by
  rcases C.strict with hs | hs
  · obtain ⟨name,hj3,he⟩ := C.first_strict_sporadic_quotient hchoice hmany hn hna hs
    refine ⟨name,?_,.inl ⟨hs,he⟩⟩
    by_contra! h
    exact C.impossible_of_first_strict_seven_sporadic_quotient hchoice hmany hn hna hs
      hj3 h.1 h.2.1 h.2.2 he
  · obtain ⟨name,hj3,he⟩ := C.second_strict_sporadic_quotient hchoice hmany hn hna hs
    refine ⟨name,?_,.inr ⟨hs,he⟩⟩
    by_contra! h
    exact C.impossible_of_second_strict_seven_sporadic_quotient hchoice hmany hn hna hs
      hj3 h.1 h.2.1 h.2.2 he

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness

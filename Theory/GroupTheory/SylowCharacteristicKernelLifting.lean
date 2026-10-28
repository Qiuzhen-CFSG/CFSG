module

public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueResidualLayer
public import Mathlib.GroupTheory.Exponent

/-!
# The final characteristic-kernel step in Niles Theorem B

This is the last paragraph of Niles (1979), printed p.62.  The central-chief
reduction and the Main Hypothesis classification are earlier source inputs.
Once the prime residual centralizes the reduction kernel, every characteristic
Sylow subgroup contained in that kernel is ambient-normal and hence trivial.
Consequently lower-central and power identities of the Sylow image lift.

The central-chief reduction and the quotient structure are separate source
inputs; this module proves their final lifting step.
-/

public section

open Subgroup

namespace Theory.GroupTheory

variable {H X : Type*} [Group H] [Finite H] [Group X]

/-- The literal last hypothesis of Niles Theorem B. -/
@[expose] def NoCharacteristicNormal (S : Subgroup H) : Prop :=
  ∀ A : Subgroup S, A.Characteristic → (A.map S.subtype).Normal → A = ⊥

/-- The residual-centralized kernel turns a characteristic Sylow subgroup into
an ambient normal subgroup. -/
theorem characteristic_image_normal_of_residual_centralizes
    {p : ℕ} [Fact p.Prime] (S : Sylow p H) (Z : Subgroup H)
    (hZ : pResidual p H ≤ centralizer (Z : Set H))
    (A : Subgroup S) [A.Characteristic]
    (hAZ : A.map (S : Subgroup H).subtype ≤ Z) :
    (A.map (S : Subgroup H).subtype).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top S]
  apply sup_le
  · exact (hZ.trans (centralizer_le hAZ)).trans (centralizer_le_normalizer _)
  · exact (S : Subgroup H).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (S : Subgroup H) A)

theorem characteristic_eq_bot_of_residual_centralizes
    {p : ℕ} [Fact p.Prime] (S : Sylow p H)
    (hno : NoCharacteristicNormal (S : Subgroup H)) (Z : Subgroup H)
    (hZ : pResidual p H ≤ centralizer (Z : Set H))
    (A : Subgroup S) [A.Characteristic]
    (hAZ : A.map (S : Subgroup H).subtype ≤ Z) : A = ⊥ :=
  hno A inferInstance
    (characteristic_image_normal_of_residual_centralizes S Z hZ A hAZ)

/-- Every lower-central identity of the actual Sylow image lifts through a
kernel centralized by the prime residual. -/
theorem lowerCentralSeries_eq_bot_of_image
    {p : ℕ} [Fact p.Prime] (S : Sylow p H)
    (hno : NoCharacteristicNormal (S : Subgroup H)) (f : H →* X)
    (hk : pResidual p H ≤ centralizer (f.ker : Set H)) (n : ℕ)
    (hn : ((S : Subgroup H).map f).lowerCentralSeries n = ⊥) :
    (⊤ : Subgroup S).lowerCentralSeries n = ⊥ := by
  let A := (⊤ : Subgroup S).lowerCentralSeries n
  apply characteristic_eq_bot_of_residual_centralizes S hno f.ker hk A
  apply (Subgroup.map_eq_bot_iff _).mp
  change (((⊤ : Subgroup S).lowerCentralSeries n).map (S : Subgroup H).subtype).map f = ⊥
  rw [top_subtype_lowerCentralSeries, map_lowerCentralSeries, hn]

/-- The Sylow class bound follows from the corresponding bound on its actual
image; nilpotence of the source is supplied by its prime-group structure. -/
theorem nilpotencyClass_le_of_image
    {p : ℕ} [Fact p.Prime] (S : Sylow p H)
    (hno : NoCharacteristicNormal (S : Subgroup H)) (f : H →* X)
    (hk : pResidual p H ≤ centralizer (f.ker : Set H)) (n : ℕ)
    (hn : ((S : Subgroup H).map f).lowerCentralSeries n = ⊥) :
    Group.nilpotencyClass S ≤ n := by
  let _ := S.isPGroup'.isNilpotent
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
    (lowerCentralSeries_eq_bot_of_image S hno f hk n hn)

/-- Fixed-degree power identities lift by the same characteristic-kernel
argument, without an abelian or splitting assumption. -/
theorem pow_eq_one_of_image
    {p : ℕ} [Fact p.Prime] (S : Sylow p H)
    (hno : NoCharacteristicNormal (S : Subgroup H)) (f : H →* X)
    (hk : pResidual p H ≤ centralizer (f.ker : Set H)) (n : ℕ)
    (hn : ∀ s : S, f s ^ n = 1) : ∀ s : S, s ^ n = 1 := by
  let A := closure (Set.range (fun s : S => s ^ n))
  let _ : A.Characteristic := closure_range_pow_characteristic n
  have hAk : A.map (S : Subgroup H).subtype ≤ f.ker := by
    rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro _ ⟨s, rfl⟩
    change f (s ^ n) = 1
    simpa only [map_pow] using hn s
  have hAb := characteristic_eq_bot_of_residual_centralizes S hno f.ker hk A hAk
  intro s
  exact (mem_bot.mp (hAb ▸ (subset_closure ⟨s, rfl⟩ : s ^ n ∈ A)))

/-- The p=2 final lift needed after the earlier Niles source results: class at
most two and exponent dividing four. Exactness comes from a nonabelian image. -/
theorem class_two_exponent_four_bounds_of_image
    (S : Sylow 2 H) (hno : NoCharacteristicNormal (S : Subgroup H))
    (f : H →* X) (hk : pResidual 2 H ≤ centralizer (f.ker : Set H))
    (hclass : ((S : Subgroup H).map f).lowerCentralSeries 2 = ⊥)
    (hpow : ∀ s : S, f s ^ 4 = 1) :
    Group.nilpotencyClass S ≤ 2 ∧ ∀ s : S, s ^ 4 = 1 :=
  ⟨nilpotencyClass_le_of_image S hno f hk 2 hclass,
    pow_eq_one_of_image S hno f hk 4 hpow⟩

/-- Central ambient chief factors in the actual kernel imply the residual
centralization used in the final paragraph of Niles Theorem B. -/
theorem residual_le_centralizer_of_central_chief_series
    (Z : Subgroup H) [Z.Normal] (hZ : IsPGroup 2 Z)
    (s : NoncentralChiefRefinement.SeriesOn Z)
    (hc : ∀ i, s.Central i) :
    pResidual 2 H ≤ centralizer (Z : Set H) := by
  have hp : IsPGroup 2 s.series.last.val :=
    hZ.of_equiv (MulEquiv.subgroupCongr (congrArg Subtype.val s.last_eq)).symm
  have hh := s.series.residual_commutator_le_head_of_central_steps hp hc
  rw [s.head_eq, s.last_eq] at hh
  change ⁅Z, pResidual 2 H⁆ ≤ ⊥ at hh
  rw [commutator_comm] at hh
  exact (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hh))

/-- The literal final Theorem B consumer: the earlier central-chief reduction
and the Main Hypothesis bounds imply the original Sylow bounds. All actions
and maps here are the original quotient map and its actual Sylow image. -/
theorem class_two_exponent_four_bounds_of_central_chief_kernel
    (S : Sylow 2 H) (hno : NoCharacteristicNormal (S : Subgroup H))
    (f : H →* X) (hp : IsPGroup 2 f.ker)
    (s : NoncentralChiefRefinement.SeriesOn f.ker)
    (hc : ∀ i, s.Central i)
    (hclass : ((S : Subgroup H).map f).lowerCentralSeries 2 = ⊥)
    (hpow : ∀ s : S, f s ^ 4 = 1) :
    Group.nilpotencyClass S ≤ 2 ∧ ∀ s : S, s ^ 4 = 1 :=
  class_two_exponent_four_bounds_of_image S hno f
    (residual_le_centralizer_of_central_chief_series f.ker hp s hc) hclass hpow

/-- Exact class and exponent are preserved, since the original Sylow also
surjects onto the image which supplies the lower bounds. -/
theorem class_two_exponent_four_of_image
    (S : Sylow 2 H) (hno : NoCharacteristicNormal (S : Subgroup H))
    (f : H →* X) (hk : pResidual 2 H ≤ centralizer (f.ker : Set H))
    (hclass : Group.nilpotencyClass ((S : Subgroup H).map f) = 2)
    (hexp : Monoid.exponent ((S : Subgroup H).map f) = 4) :
    Group.nilpotencyClass S = 2 ∧ Monoid.exponent S = 4 := by
  let _ := S.isPGroup'.isNilpotent
  let _ : Finite ((S : Subgroup H).map f) :=
    Finite.of_surjective (f.subgroupMap (S : Subgroup H)) (f.subgroupMap_surjective _)
  let _ := (S.isPGroup'.map f).isNilpotent
  have hclass' : ((S : Subgroup H).map f).lowerCentralSeries 2 = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_of_nilpotencyClass_le hclass.le
  have hpow : ∀ t : S, f t ^ 4 = 1 := by
    intro t
    have ht := Monoid.pow_exponent_eq_one
      (⟨f t, mem_map_of_mem f t.property⟩ : (S : Subgroup H).map f)
    rw [hexp] at ht
    exact congrArg Subtype.val ht
  obtain ⟨hcl, hpowS⟩ := class_two_exponent_four_bounds_of_image
    S hno f hk hclass' hpow
  constructor
  · apply le_antisymm hcl
    calc
      2 = Group.nilpotencyClass ((S : Subgroup H).map f) := hclass.symm
      _ ≤ Group.nilpotencyClass S :=
        Group.nilpotencyClass_le_of_surjective (f.subgroupMap (S : Subgroup H))
          (f.subgroupMap_surjective _)
  · apply Nat.dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one hpowS)
    rw [← hexp]
    exact MonoidHom.exponent_dvd (f.subgroupMap_surjective (S : Subgroup H))

/-- The full exact final-step consumer with the central-chief kernel supplied
by the earlier source reduction. -/
theorem class_two_exponent_four_of_central_chief_kernel
    (S : Sylow 2 H) (hno : NoCharacteristicNormal (S : Subgroup H))
    (f : H →* X) (hp : IsPGroup 2 f.ker)
    (s : NoncentralChiefRefinement.SeriesOn f.ker)
    (hc : ∀ i, s.Central i)
    (hclass : Group.nilpotencyClass ((S : Subgroup H).map f) = 2)
    (hexp : Monoid.exponent ((S : Subgroup H).map f) = 4) :
    Group.nilpotencyClass S = 2 ∧ Monoid.exponent S = 4 :=
  class_two_exponent_four_of_image S hno f
    (residual_le_centralizer_of_central_chief_series f.ker hp s hc) hclass hexp

/-- The canonical quotient form matches Niles Theorem 7.2 without transporting
a chosen chief series along an equality of quotient kernels. -/
theorem class_two_exponent_four_of_central_quotient
    (S : Sylow 2 H) (hno : NoCharacteristicNormal (S : Subgroup H))
    (Z : Subgroup H) [Z.Normal] (hp : IsPGroup 2 Z)
    (s : NoncentralChiefRefinement.SeriesOn Z) (hc : ∀ i, s.Central i)
    (hclass : Group.nilpotencyClass
      ((S : Subgroup H).map (QuotientGroup.mk' Z)) = 2)
    (hexp : Monoid.exponent
      ((S : Subgroup H).map (QuotientGroup.mk' Z)) = 4) :
    Group.nilpotencyClass S = 2 ∧ Monoid.exponent S = 4 := by
  apply class_two_exponent_four_of_image S hno (QuotientGroup.mk' Z) _ hclass hexp
  simpa only [QuotientGroup.ker_mk'] using
    residual_le_centralizer_of_central_chief_series Z hp s hc

end Theory.GroupTheory

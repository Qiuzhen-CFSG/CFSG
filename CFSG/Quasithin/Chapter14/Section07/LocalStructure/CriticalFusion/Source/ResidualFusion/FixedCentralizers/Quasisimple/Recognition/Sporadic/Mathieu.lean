module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.OddPrimes
public import Theory.Mathieu.SchurMultipliers.FiniteCovers
public import Theory.Mathieu.SchurMultipliers.M23Kernel
public import Theory.GroupAction.CentralCoverTwoCentral
public import Theory.Mathieu.M12.TwoCentralInvolutions.CentralizerOrder
public import Theory.Mathieu.M12.Properties.AutCover
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoCentral
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms

/-!
# Excluding the five Mathieu quotients in the fixed-component sieve

The original u gives even kernel for the marked perfect central cover,
excluding M₁₁ and M₂₃ by their native multiplier calculations. In M₁₂
and M₂₂, the genuine two-central action has centralizer order 192 and 384,
respectively. A two-group kernel cannot supply the factor of five that
the source fixed subgroup has. For M₂₄ the two-central class is 2A;
its centralizer has order 21504. Fixed-point lifting through the same
cover supplies a factor of seven, excluded by the original H/O₂(H) ≃ S₅.

Every theorem consumes the full published Source.Case and the supplied
J/O₂(J) equivalence. All class-selection and lifting premises are proved.

Source: Aschbacher–Smith 1.1.5(3)(f), printed pp.502–503, I.1.3,
printed p.407, and 14.7.68(2), printed p.1071 (PDF p.1088);
GLS3 Tables 5.3b, 5.3c and 5.3e.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- Even kernel excludes the native M₁₁ quotient. -/
theorem fixedSporadic_ne_m11 (u : F.U) {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} {name : SporadicName}
    (h : SporadicSieve.Case d u Lu α name)
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier) :
    name ≠ .m11 := by
  intro hn
  subst name
  let := h.quasisimple
  let : IsQuasisimple (Lu.subgroupOf (d.fixedCentralizer u)) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.le_centralizer).symm
  have hx := Sporadic.Mathieu.SchurMultipliers.m11_cover_kernel_not_two
    (d.fixedSporadicCover u h.le_centralizer h.quasisimple e)
  erw [d.fixedSporadicCover_kernel u h.le_centralizer h.quasisimple e] at hx
  exact hx (d.fixedComponent_twoCore_even h.generation u h.nontrivial
    h.le_centralizer h.contains.le)

/-- Even kernel excludes the native M₂₃ quotient. -/
theorem fixedSporadic_ne_m23 (u : F.U) {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} {name : SporadicName}
    (h : SporadicSieve.Case d u Lu α name)
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier) :
    name ≠ .m23 := by
  intro hn
  subst name
  have hx := Sporadic.Mathieu.SchurMultipliers.m23_cover_kernel_not_two
    (d.fixedSporadicCover u h.le_centralizer h.quasisimple e)
  erw [d.fixedSporadicCover_kernel u h.le_centralizer h.quasisimple e] at hx
  exact hx (d.fixedComponent_twoCore_even h.generation u h.nontrivial
    h.le_centralizer h.contains.le)

/-- The source factor of five excludes the two-central M₁₂ quotient. -/
theorem fixedSporadic_ne_m12 (u : F.U) {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} {name : SporadicName}
    (h : SporadicSieve.Case d u Lu α name)
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier) :
    name ≠ .m12 := by
  intro hn
  subst name
  let := h.quasisimple
  let : IsQuasisimple (Lu.subgroupOf (d.fixedCentralizer u)) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.le_centralizer).symm
  let f := d.fixedSporadicCover u h.le_centralizer h.quasisimple e
  obtain ⟨P, hP⟩ := h.twoCentral.2.2
  obtain ⟨t, ht, htc, heq⟩ := MulAut.exists_twoCentral_model_of_central_cover
    f.toMonoidHom f.surjective f.ker_le_center Sporadic.Mathieu.m12_center_eq_bot
    α h.twoCentral.1 h.twoCentral.2.1 P (fun x hx => hP ⟨x, hx⟩)
  have hk : IsPGroup 2 f.toMonoidHom.ker := by
    dsimp [f]
    rw [d.fixedSporadicCover_kernel]
    exact pCore_isPGroup
  have hb : ¬ 5 ∣ Nat.card (MulAut.conj t).fixedSubgroup := by
    erw [MulAut.fixedSubgroup_conj,
      Sporadic.Mathieu.M12Involutions.card_centralizer_of_twoCentral t ht htc]
    decide
  exact MulAut.odd_prime_not_dvd_card_fixedSubgroup_of_cover α (MulAut.conj t)
    f.toMonoidHom heq hk (by decide) (by decide) hb
    (d.five_dvd_card_fixedComponent_fixedSubgroup u h.le_centralizer h.contains.le
      α h.conjugation)

/-- The source factor of five excludes the M₂₂ quotient. -/
theorem fixedSporadic_ne_m22 (u : F.U) {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} {name : SporadicName}
    (h : SporadicSieve.Case d u Lu α name)
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier) :
    name ≠ .m22 := by
  intro hn
  subst name
  let := h.quasisimple
  let : IsQuasisimple (Lu.subgroupOf (d.fixedCentralizer u)) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.le_centralizer).symm
  let f := d.fixedSporadicCover u h.le_centralizer h.quasisimple e
  obtain ⟨P, hP⟩ := h.twoCentral.2.2
  obtain ⟨t, ht, _, heq⟩ := MulAut.exists_twoCentral_model_of_central_cover
    f.toMonoidHom f.surjective f.ker_le_center Sporadic.Mathieu.m22_center_eq_bot
    α h.twoCentral.1 h.twoCentral.2.1 P (fun x hx => hP ⟨x, hx⟩)
  have hk : IsPGroup 2 f.toMonoidHom.ker := by
    dsimp [f]
    rw [d.fixedSporadicCover_kernel]
    exact pCore_isPGroup
  have hb : ¬ 5 ∣ Nat.card (MulAut.conj t).fixedSubgroup := by
    erw [MulAut.fixedSubgroup_conj,
      Sporadic.Mathieu.M22FourNormalizers.involution_centralizer_card t ht]
    decide
  exact MulAut.odd_prime_not_dvd_card_fixedSubgroup_of_cover α (MulAut.conj t)
    f.toMonoidHom heq hk (by decide) (by decide) hb
    (d.five_dvd_card_fixedComponent_fixedSubgroup u h.le_centralizer h.contains.le
      α h.conjugation)

/-- The lifted factor of seven excludes the two-central M₂₄ quotient. -/
theorem fixedSporadic_ne_m24 (u : F.U) {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} {name : SporadicName}
    (h : SporadicSieve.Case d u Lu α name)
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier) :
    name ≠ .m24 := by
  intro hn
  subst name
  let := h.quasisimple
  let : IsQuasisimple (Lu.subgroupOf (d.fixedCentralizer u)) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.le_centralizer).symm
  let f := d.fixedSporadicCover u h.le_centralizer h.quasisimple e
  obtain ⟨P, hP⟩ := h.twoCentral.2.2
  obtain ⟨t, ht, htc, heq⟩ := MulAut.exists_twoCentral_model_of_central_cover
    f.toMonoidHom f.surjective f.ker_le_center
    Sporadic.Mathieu.M24InvolutionCentralizers.center_eq_bot
    α h.twoCentral.1 h.twoCentral.2.1 P (fun x hx => hP ⟨x, hx⟩)
  have hs := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed α (MulAut.conj t)
    f.toMonoidHom f.surjective f.ker_le_center heq
    ((orderOf_eq_prime_iff.mp h.twoCentral.2.1).1) P (fun x hx => hP ⟨x, hx⟩)
  have hd := card_dvd_of_surjective _ hs
  have hseven : 7 ∣ Nat.card (MulAut.conj t).fixedSubgroup := by
    erw [MulAut.fixedSubgroup_conj,
      Sporadic.Mathieu.M24InvolutionCentralizers.card_centralizer_of_twoCentral t ht htc]
    decide
  exact d.not_seven_dvd_card_fixedComponent_fixedSubgroup u h.le_centralizer α h.conjugation
    (hseven.trans hd)


end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

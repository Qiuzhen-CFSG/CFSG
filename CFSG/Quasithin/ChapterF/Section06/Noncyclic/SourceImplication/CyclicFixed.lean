module

public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ThreeResidual
public import CFSG.Quasithin.Defs
public import Theory.GroupAction.MarkedCubicClassTwo
public import Theory.GroupTheory.PCoreFrattiniQuotient
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The source cyclic-centralizer bound on every marked quotient

A.1.31(1) is retained as a universal implication on a genuine quotient:
its rank hypothesis belongs to the group before quotienting, and its
conclusion requires the quotient's generalized Fitting subgroup to be
its prime core. Surjective maps present those quotients without choosing
an identification of the codomain with a quotient type.

In the three-residual branch, the generalized Fitting hypothesis is proved
from the two-core condition and the two-group quotient. The actual SQTK
cover then gives cyclic fixed subgroups for involutions on the residual.
Coprime fixed-point lifting passes cyclicity to every compatible quotient,
which discharges the fixed-point input of the marked class-two argument.
The universal A.1.31 input remains with qt-a-01-section-rank and the final
source assembly owner qt-f06-noncyclic.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
A.1.31(1) and F.6.16, printed pp.27–28, 308 (1 March 2004 manuscript).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Noncyclic
universe u v

/-- A.1.31(1), with a quotient presented by an arbitrary surjective map.
The rank hypothesis is on the source of the map. -/
@[expose] def SectionCentralizerInput : Prop :=
  ∀ (A : Type u) [Group A] [Finite A] (D : Type v) [Group D] [Finite D]
    (p : ℕ) [Fact p.Prime], Odd p → primeRank p A ≤ 2 →
    ∀ f : A →* D, Function.Surjective f → generalizedFitting D = pCore p D →
    ∀ S : Subgroup D, IsPGroup 2 S → S ≠ ⊥ →
      IsCyclic ((centralizer (S : Set D)).subgroupOf (pCore p D))

variable {G : Type*} [Group G] [Finite G]

/-- In the three-group branch the residual is the generalized Fitting subgroup. -/
theorem generalizedFitting_eq_threeCore_of_three_residual
    (hcore : pCore 2 G = ⊥) (hL : IsPGroup 3 (pResidual 2 G)) :
    generalizedFitting G = pCore 3 G := by
  apply Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing
  apply centralizer_pCore_le_of_quotient_isPGroup 3 2 hcore
  exact (isPGroup_quotient_pResidual (G := G) 2).of_equiv
    (QuotientGroup.quotientMulEquivOfEq (residual_eq_threeCore hL))

/-- Cyclic fixed subgroups descend to every compatible odd-order quotient.
The quotient kernel need only be invariant under the displayed automorphism. -/
theorem cyclic_fixed_quotient_of_cyclic_fixed
    (hodd : Odd (Nat.card G)) (a : MulAut G) (ha : a ^ 2 = 1)
    (hc : IsCyclic a.fixedSubgroup)
    (N : Subgroup G) [N.Normal] (b : MulAut (G ⧸ N))
    (hb : ∀ x, b (QuotientGroup.mk' N x) = QuotientGroup.mk' N (a x)) :
    IsCyclic b.fixedSubgroup := by
  let : IsCyclic a.fixedSubgroup := hc
  let q := QuotientGroup.mk' N
  let f : a.fixedSubgroup →* b.fixedSubgroup :=
    (q.comp a.fixedSubgroup.subtype).codRestrict _ (fun x => by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      change b (q x) = q x
      rw [hb, (MulAut.mem_fixedSubgroup _ _).mp x.property])
  have hb2 : b ^ 2 = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    change b (b (q y)) = q y
    rw [hb, hb, show a (a y) = y from DFunLike.congr_fun ha y]
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hax, hqx⟩ := MulAut.exists_fixed_preimage_of_odd_card hodd
      (hodd.of_dvd_nat (card_quotient_dvd_card N)) a b
      (fun x => DFunLike.congr_fun ha x) (fun x => DFunLike.congr_fun hb2 x)
      q (QuotientGroup.mk'_surjective N) (fun x => (hb x).symm) y ((MulAut.mem_fixedSubgroup _ _).mp y.property)
    exact ⟨⟨x, (MulAut.mem_fixedSubgroup _ _).mpr hax⟩, Subtype.ext hqx⟩
  exact isCyclic_of_surjective f hf

/-- The quotient fixed-point contract follows from the two original centralizers. -/
theorem quotientCyclicFixed_of_fixed
    (hP : IsPGroup 3 G) (a b : MulAut G) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hca : IsCyclic a.fixedSubgroup) (hcb : IsCyclic b.fixedSubgroup) :
    MarkedCubicClassTwo.QuotientCyclicFixed a b := by
  have hodd : Odd (Nat.card G) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  intro N hN _ aN bN haN hbN
  let := hN
  exact ⟨cyclic_fixed_quotient_of_cyclic_fixed hodd a ha hca N aN haN,
    cyclic_fixed_quotient_of_cyclic_fixed hodd b hb hcb N bN hbN⟩

/-- A.1.31 applies to the actual SQTK cover, and hence to conjugation on L. -/
theorem residual_involution_fixed_cyclic
    {G : Type u} [Group G] [Finite G]
    {Ghat : Type u} [Group Ghat] [Finite Ghat] {K : GroupClass.{u}}
    (source : SectionCentralizerInput.{u,u})
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (hcore : pCore 2 G = ⊥) (hL : IsPGroup 3 (pResidual 2 G))
    (t : G) (ht : orderOf t = 2) :
    IsCyclic (MulAut.conjNormal t : MulAut (pResidual 2 G)).fixedSubgroup := by
  let f := e.symm.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 3 Ghat))
  have hf : Function.Surjective f := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hS : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht, pow_one])
  have hSne : zpowers t ≠ ⊥ := by
    intro hb
    have he : t = 1 := mem_bot.mp (hb ▸ mem_zpowers t)
    simp [he] at ht
  have hc := source Ghat G 3 (by decide)
    (hhat.stronglyQuasithin 3 Nat.prime_three (by decide)) f hf
    (generalizedFitting_eq_threeCore_of_three_residual hcore hL) (zpowers t) hS hSne
  let : IsCyclic ((centralizer (zpowers t : Set G)).subgroupOf (pCore 3 G)) := hc
  let a : MulAut (pResidual 2 G) := MulAut.conjNormal t
  let g : a.fixedSubgroup →* (centralizer (zpowers t : Set G)).subgroupOf (pCore 3 G) :=
    { toFun := fun x => ⟨⟨x.val.val, (residual_eq_threeCore hL).le x.val.property⟩, by
        have he := congrArg Subtype.val ((MulAut.mem_fixedSubgroup a x.val).mp x.property)
        change t * x.val.val * t⁻¹ = x.val.val at he
        have hcomm : t ∈ centralizer ({x.val.val} : Set G) :=
          mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
        have hle : zpowers t ≤ centralizer ({x.val.val} : Set G) := zpowers_le.mpr hcomm
        intro y hy
        exact mem_centralizer_singleton_iff.mp (hle hy)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply isCyclic_of_injective g
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (centralizer (zpowers t : Set G)).subgroupOf (pCore 3 G) => z.val.val) he

end CFSG.Quasithin.ChapterF.Noncyclic

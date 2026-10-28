module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.OddPrimes
public import Theory.GroupAction.SylowFixedCentralQuotient
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.Reduction
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.CentralizerCertificate
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB

/-!
# Seven excludes the actual J₄ and Held quotients

Both J₄ involution centralizers have order divisible by seven. The checked
class coverage and the literal full-centralizer orders prove this on the
binary matrix carrier. The same holds for both Held inner involution rows:
their actual centralizers have orders 161280 and 21504, including the
2-central 2B row. Thus no extra class-selection premise is needed.

For the source's perfect central cover J → J/O₂(J) → S, the given inner
automorphism induces conjugation by the image of its implementer. Perfectness
and centrality of the kernel show that this induced involution is nontrivial.
The original fixed Sylow two-subgroup supplies fixed-point lifting, so the
model's factor of seven divides the order of the original fixed subgroup.
Its actual inclusion into H contradicts the proved S₅ quotient bound.

The four source applications retain the original quotient equivalence and
ambient conjugation by z; no centralizer row or divisibility is assumed.

Source: Aschbacher–Smith, 14.7.68(2), printed p.1071 (PDF p.1088), and
1.1.5(3)(f), printed pp.502–503; GLS3 Tables 5.3i and 5.3p. The imported
model certificates retain their ATLAS source attribution.
-/

public section

open Subgroup Theory.GroupTheory
noncomputable section

private theorem fixed_card_conj {A : Type*} [Group A] {x y : A} (h : IsConj x y) :
    Nat.card (MulAut.conj x).fixedSubgroup = Nat.card (MulAut.conj y).fixedSubgroup := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have he := Nat.card_congr (MulAut.fixedSubgroupCongr (MulAut.conj c) (MulAut.conj x)).toEquiv
  rw [MulAut.congr_conj] at he
  exact he.trans (congrArg (fun z : A => Nat.card (MulAut.conj z).fixedSubgroup) hc)

private theorem j4_center : center Janko4.Model = ⊥ := by
  let C := Janko4.InvolutionCentralizers.First.centralizer
  let aC : C := ⟨Janko4.a, mem_centralizer_singleton_iff.mpr rfl⟩
  let z : center C := ⟨aC, mem_center_iff.mpr (fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.mp y.property))⟩
  have hz : z ≠ 1 := by
    intro h
    have ha : Janko4.a = 1 := congrArg (fun t : center C => ((t : C) : Janko4.Model)) h
    have ho := Janko4.orderOf_a
    rw [ha, orderOf_one] at ho
    contradiction
  have hc := (Nat.card_eq_two_iff' (1 : center C)).mp
    Janko4.InvolutionCentralizers.First.centralizer_center_card
  apply le_bot_iff.mp
  intro x hx
  by_contra hx1
  have hxc : x ∈ C := (center_le_centralizer _) hx
  let w : center C := ⟨⟨x, hxc⟩, mem_center_iff.mpr (fun y =>
    Subtype.ext (mem_center_iff.mp hx y))⟩
  have hw : w ≠ 1 := by
    intro hw
    exact hx1 (show x = 1 from congrArg (fun t : center C => ((t : C) : Janko4.Model)) hw)
  have he : x = Janko4.a := congrArg (fun t : center C => ((t : C) : Janko4.Model))
    (hc.unique hw hz)
  exact Janko4.a_mul_b_ne_b_mul_a (he ▸ (mem_center_iff.mp hx Janko4.b).symm)

private theorem j4_seven (y : Janko4.Model) (hy : orderOf (MulAut.conj y) = 2) :
    7 ∣ Nat.card (MulAut.conj y).fixedSubgroup := by
  have ho : orderOf y = 2 := (MulAut.conj_orderOf_of_center_eq_bot j4_center y).symm.trans hy
  have hfirst : 7 ∣ Nat.card (MulAut.conj Janko4.a).fixedSubgroup := by
    rw [MulAut.fixedSubgroup_conj, Janko4.OuterReduction.OddIndex.modelCentralizer_card]
    norm_num
  have hseed : 7 ∣ Nat.card
      (MulAut.conj (Janko4.InvolutionCentralizers.Second.seed : Janko4.Model)).fixedSubgroup := by
    rw [MulAut.fixedSubgroup_conj]
    change 7 ∣ Nat.card Janko4.InvolutionCentralizers.Second.ambientCentralizer
    rw [Janko4.InvolutionCentralizers.Second.ambient_card]
    norm_num
  have hsecond : 7 ∣ Nat.card
      (MulAut.conj ((Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b) ^ 5)).fixedSubgroup := by
    obtain ⟨c, hc⟩ := Janko4.Simplicity.Max1Fusion.seed_fuses_second
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four
    have hw : Janko4.Simplicity.word
        (Janko4.Simplicity.a Janko4.matrixA_mul_self)
        (Janko4.Simplicity.b Janko4.matrixB_pow_four) "ababb" =
        Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b := by
      change Janko4.Simplicity.word Janko4.a Janko4.b "ababb" = _
      simp [Janko4.Simplicity.word, mul_assoc]
    rw [hw] at hc
    have hf := fixed_card_conj (isConj_iff.mpr ⟨c, hc.symm⟩)
    exact hf ▸ hseed
  rcases Janko4.OuterReduction.involution_isConj_of_max1_odd_index
    Janko4.OuterReduction.max1_odd_index_unconditional ho with h | h
  · exact fixed_card_conj h ▸ hfirst
  · exact fixed_card_conj h ▸ hsecond

private theorem held_seven (y : Held.He) (hy : orderOf (MulAut.conj y) = 2) :
    7 ∣ Nat.card (MulAut.conj y).fixedSubgroup := by
  have ho : orderOf y = 2 := (Held.InvolutionFixedData.orderOf_conj y).symm.trans hy
  rcases Held.InvolutionFixedData.Coverage.innerInvolutionCoverage y ho with
    ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [← fixed_card_conj (x := Held.a) (y := (MulAut.conj c) Held.a)
      (isConj_iff.mpr ⟨c, rfl⟩)]
    change 7 ∣ Nat.card Held.InvolutionFixedData.TwoA.centralizer
    rw [Held.InvolutionFixedData.TwoA.CentralizerCertificate.centralizer_card]
    norm_num
  · rw [← fixed_card_conj (x := Held.TwoLocalCandidates.max5First ^ 4)
      (y := (MulAut.conj c) (Held.TwoLocalCandidates.max5First ^ 4))
      (isConj_iff.mpr ⟨c, rfl⟩)]
    rw [Held.InvolutionFixedData.twoB_fixedSubgroup_card]
    norm_num

open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure

private theorem seven_of_cover {A B : Type*} [Group A] [Finite A] [Group B]
    (f : PerfectCentralCovering.Cover A B) (α : MulAut A) (hα : TwoCentralInner α)
    (hseven : ∀ y : B, orderOf (MulAut.conj y) = 2 →
      7 ∣ Nat.card (MulAut.conj y).fixedSubgroup) :
    7 ∣ Nat.card α.fixedSubgroup := by
  let := f.isPerfect
  obtain ⟨⟨x, hx⟩, ho, P, hP⟩ := hα
  let β := MulAut.conj (f.toMonoidHom x)
  have heq (a : A) : f.toMonoidHom (α a) = β (f.toMonoidHom a) := by
    rw [← hx]
    simp only [β, MulAut.conj_apply, map_mul, map_inv]
  have ha2 : α ^ 2 = 1 := ho ▸ pow_orderOf_eq_one α
  have hb2 : β ^ 2 = 1 := by
    ext b
    obtain ⟨a, rfl⟩ := f.surjective b
    change β (β (f.toMonoidHom a)) = f.toMonoidHom a
    rw [← heq, ← heq]
    exact congrArg f.toMonoidHom (show α (α a) = a from
      DFunLike.congr_fun ha2 a)
  have hbne : β ≠ 1 := by
    intro hb
    have ha : α = 1 := MulAut.eq_one_of_central_displacement α (fun a => by
      apply f.ker_le_center
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, hb, MulAut.one_apply, inv_mul_cancel])
    rw [ha, orderOf_one] at ho
    contradiction
  have hb : orderOf β = 2 := orderOf_eq_prime hb2 hbne
  have hsurj := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed α β f.toMonoidHom
    f.surjective f.ker_le_center heq ha2 P (fun a ha => hP ⟨a, ha⟩)
  exact (hseven _ hb).trans (card_dvd_of_surjective _ hsurj)

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SporadicSieve
open CFSG.Quasithin.Chapter12.Section08 CFSG.Quasithin.ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {d : Data T L V F W} {u : F.U} {Lu : Subgroup G}
  {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} {name : SporadicName}

/-- The J₄ quotient forces seven in the original fixed subgroup. -/
theorem Case.seven_dvd_fixedSubgroup_of_j4 (h : Case d u Lu α name)
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier)
    (hn : name = .j4) : 7 ∣ Nat.card α.fixedSubgroup := by
  subst name
  exact seven_of_cover (d.fixedSporadicCover u h.le_centralizer h.quasisimple e)
    α h.twoCentral j4_seven

/-- The Held quotient forces seven in the original fixed subgroup. -/
theorem Case.seven_dvd_fixedSubgroup_of_he (h : Case d u Lu α name)
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier)
    (hn : name = .he) : 7 ∣ Nat.card α.fixedSubgroup := by
  subst name
  exact seven_of_cover (d.fixedSporadicCover u h.le_centralizer h.quasisimple e)
    α h.twoCentral held_seven

/-- J₄ is excluded using the original ambient fixed-subgroup bound. -/
theorem Case.not_j4 (h : Case d u Lu α name)
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier) : name ≠ .j4 := by
  intro hn
  exact d.not_seven_dvd_card_fixedComponent_fixedSubgroup u h.le_centralizer α h.conjugation
    (h.seven_dvd_fixedSubgroup_of_j4 e hn)

/-- Held is excluded using the original ambient fixed-subgroup bound. -/
theorem Case.not_he (h : Case d u Lu α name)
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier) : name ≠ .he := by
  intro hn
  exact d.not_seven_dvd_card_fixedComponent_fixedSubgroup u h.le_centralizer α h.conjugation
    (h.seven_dvd_fixedSubgroup_of_he e hn)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SporadicSieve

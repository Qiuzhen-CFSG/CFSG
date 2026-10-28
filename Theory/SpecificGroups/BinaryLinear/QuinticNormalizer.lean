module
public import Theory.SpecificGroups.BinaryLinear.FiveTwoLocalFive
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SolvableFiveFree
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalOvergroups
public import Theory.GroupAction.FiveThirtyTwoCentralizer
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Quintic actors and two-local normalizers in binary dimension five

A five-element has odd centralizer in GL₅(2). Orbit counting on a
normalized nontrivial two-subgroup, together with the existing upper bound
of sixteen, therefore gives order sixteen exactly. Its full normalizer
is a point or hyperplane parabolic and contains a full Sylow two-subgroup.
A solvable subgroup normalized by that normalizer cannot have order divisible
by five, by the binary flag-overgroup theorem. The final theorem retains an
actual SL₅(2) marking, an invariant two-subgroup and the inner actor subgroup.

Source: Aschbacher--Smith 14.6.15, printed p.1035, the binary-five row in
C.2.7; the actual consumer is Quintic.SourceComponent.BinaryFive.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryLinear.QuinticNormalizer
open OuterCyclic
private instance : Finite (LinearGroup 5) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) (matrixEquivLinear 5).toEquiv

private def natural : LinearGroup 5 →* MulAut (Multiplicative (Space 5)) where
  toFun g := g.toAddEquiv.toMultiplicative
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

private theorem natural_injective : Function.Injective natural := by
  intro g h hh
  apply LinearEquiv.ext
  intro v
  exact congrArg Multiplicative.toAdd (MulEquiv.congr_fun hh (Multiplicative.ofAdd v))

private theorem centralizer_five (A : Subgroup (LinearGroup 5)) (hA : Nat.card A = 5) :
    Nat.card (centralizer (A : Set (LinearGroup 5))) ∣ 15 := by
  let V := Multiplicative (Space 5)
  let : MulDistribMulAction (LinearGroup 5) V := MulDistribMulAction.compHom V natural
  let : FaithfulSMul (LinearGroup 5) V := ⟨by
    intro a b hab
    apply natural_injective
    apply MulEquiv.ext
    intro v
    exact hab v⟩
  have hV : Nat.card V = 32 := by
    change Nat.card (Fin 5 → ZMod 2) = 32
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    decide
  exact Subgroup.FiveThirtyTwo.centralizer_card_dvd_fifteen (V := V) A hA hV

/-- Every nontrivial two-subgroup normalized by a quintic element has order sixteen. -/
theorem card_sixteen (U : Subgroup (LinearGroup 5)) (hU : IsPGroup 2 U) (hne : U ≠ ⊥)
    (hfive : 5 ∣ Nat.card (normalizer (U : Set (LinearGroup 5)))) : Nat.card U = 16 := by
  have hle := FiveTwoLocalFive.card_le_sixteen U hU hfive
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  let A := zpowers (g : LinearGroup 5)
  have hA : Nat.card A = 5 := by
    rw [Nat.card_zpowers]
    exact (Subgroup.orderOf_coe g).trans hg
  have hAU : A ≤ normalizer (U : Set (LinearGroup 5)) := zpowers_le.mpr g.property
  let : MulDistribMulAction A U := conjMulDistribMulActionOfLeNormalizer A U hAU
  obtain ⟨m,hm⟩ := hU.exists_card_eq
  have hdis : Disjoint U (centralizer (A : Set (LinearGroup 5))) := by
    apply disjoint_of_coprime_natCard
    rw [hm]
    exact ((Nat.Coprime.of_dvd_right (centralizer_five A hA)
      (by decide : Nat.Coprime 2 15))).pow_left m
  have hfixed : FixedPoints.subgroup A U = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hdis.eq_bot]
    refine ⟨u.property,mem_centralizer_iff.mpr ?_⟩
    intro a ha
    have he := congrArg Subtype.val (hu (⟨a,ha⟩ : A))
    change a * (u : LinearGroup 5) * a⁻¹ = u at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hmod := hp.card_modEq_card_fixedPoints U
  change Nat.card U % 5 = Nat.card (FixedPoints.subgroup A U) % 5 at hmod
  rw [hfixed,card_bot] at hmod
  have hm4 : m ≤ 4 := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp (hm ▸ hle)
  have hgt : 1 < Nat.card U := Finite.one_lt_card_iff_nontrivial.mpr
    ((nontrivial_iff_ne_bot U).mpr hne)
  rw [hm] at hmod hgt ⊢
  interval_cases m <;> norm_num at *

/-- A quintic normalizer of a nontrivial two-subgroup is a full endpoint parabolic. -/
theorem normalizer_isEndParabolic (U : Subgroup (LinearGroup 5))
    (hU : IsPGroup 2 U) (hne : U ≠ ⊥)
    (hfive : 5 ∣ Nat.card (normalizer (U : Set (LinearGroup 5)))) :
    FiveParabolicStabilizer.IsEndParabolic (normalizer (U : Set (LinearGroup 5))) :=
  FiveElementaryNormalizer.normalizer_isEndParabolic U hU (card_sixteen U hU hne hfive) hfive

private theorem end_sylow (P : Subgroup (LinearGroup 5))
    (hP : FiveParabolicStabilizer.IsEndParabolic P) :
    ∃ S : Sylow 2 (LinearGroup 5), (S : Subgroup _) ≤ P := by
  open FiveFlagGeometry FiveFlagGeometry.MaximalOvergroups in
    rcases hP with ⟨v,hv,rfl⟩ | ⟨f,hf,rfl⟩
    · obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace
        (Submodule.span (ZMod 2) {v}) 0 (by simpa using finrank_span_singleton hv)
      refine ⟨flagSylow b,?_⟩
      rw [flagSylow_coe,←hb,←flagStabilizer_singleton]
      exact (flag_le_iff b _ _).mpr (Set.subset_univ _)
    · have hd : Module.finrank (ZMod 2) f.ker = 4 := by
        have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
        norm_num [Space] at hh
        omega
      obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace f.ker 3 (by simpa using hd)
      refine ⟨flagSylow b,?_⟩
      rw [flagSylow_coe,←hb,←flagStabilizer_singleton]
      exact (flag_le_iff b _ _).mpr (Set.subset_univ _)

private theorem solvable_sup (A S : Subgroup (LinearGroup 5))
    [Group.IsSolvable A] [Group.IsSolvable S]
    (hS : S ≤ normalizer (A : Set (LinearGroup 5))) :
    Group.IsSolvable (A ⊔ S : Subgroup (LinearGroup 5)) := by
  let D := A ⊔ S
  let : (A.subgroupOf D).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hS)
  let : Group.IsSolvable (A.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show A ≤ D from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show A ≤ D from le_sup_left)).injective
  let : Group.IsSolvable (S.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show S ≤ D from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show S ≤ D from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top (A.subgroupOf D) (S.subgroupOf D)
    (by rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])

/-- A solvable subgroup cannot both normalize a nontrivial two-subgroup and
be normalized by its entire normalizer if its order is divisible by five. -/
theorem no_solvable_mutual_normalizer
    (U A : Subgroup (LinearGroup 5)) (hU : IsPGroup 2 U) (hne : U ≠ ⊥)
    [Group.IsSolvable A] (hA : A ≤ normalizer (U : Set (LinearGroup 5)))
    (hN : normalizer (U : Set (LinearGroup 5)) ≤ normalizer (A : Set (LinearGroup 5)))
    (hfive : 5 ∣ Nat.card A) : False := by
  obtain ⟨S,hS⟩ := end_sylow _ (normalizer_isEndParabolic U hU hne
    (hfive.trans (card_dvd_of_le hA)))
  let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  let : Group.IsSolvable (A ⊔ (S : Subgroup (LinearGroup 5)) : Subgroup _) :=
    solvable_sup A S (hS.trans hN)
  exact FiveFlagGeometry.solvable_sylow_overgroup_five_free S _ le_sup_right
    (hfive.trans (card_dvd_of_le (show A ≤ A ⊔ (S : Subgroup (LinearGroup 5)) from le_sup_left)))
/-- The same obstruction for an actual inner automorphism subgroup of SL₅(2).
The normalizer and invariant two-subgroup are retained under the marking. -/
theorem no_solvable_inner_actor {C : Type*} [Group C] [Finite C]
    (e : C ≃* SL(5,ZMod 2)) (Q : Subgroup C) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (A : Subgroup (MulAut C)) [Group.IsSolvable A]
    (hi : A ≤ MulAut.innerSubgroup C)
    (hfix : ∀ a ∈ A, Q.map a.toMonoidHom = Q)
    (hn : (normalizer (Q : Set C)).map MulAut.conj ≤ normalizer (A : Set (MulAut C)))
    (hfive : 5 ∣ Nat.card A) : False := by
  have hz : center C = ⊥ :=
    (Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e
      (Theory.SpecificGroups.BinaryComponentResidual.linear (Or.inr rfl))).1
  have hconj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let B := A.comap (MulAut.conj : C →* MulAut C)
  let f : B →* A := (MulAut.conj.comp B.subtype).codRestrict A (fun b => b.property)
  have hf : Function.Injective f := fun x y he => Subtype.ext (hconj (congrArg Subtype.val he))
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨x,hx⟩ := hi a.property
    exact ⟨⟨x,show MulAut.conj x ∈ A from hx.symm ▸ a.property⟩,Subtype.ext hx⟩
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (f := f) hf
  have hB : B ≤ normalizer (Q : Set C) := by
    intro x hx
    exact mem_normalizer_iff_map_conj_eq.mpr (hfix (MulAut.conj x) hx)
  have hNB : normalizer (Q : Set C) ≤ normalizer (B : Set C) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    have hh := mem_normalizer_iff.mp (hn (mem_map_of_mem MulAut.conj hx)) (MulAut.conj y)
    simpa only [B,mem_comap,map_mul,map_inv] using hh
  let b := e.trans (slEquivLinear 5)
  let U := Q.map b.toMonoidHom
  let D := B.map b.toMonoidHom
  let : Group.IsSolvable D := Group.isSolvable_of_surjective
    (b.toMonoidHom.subgroupMap_surjective B)
  apply no_solvable_mutual_normalizer U D (hQ.map _)
    (fun he => hne ((Q.map_eq_bot_iff_of_injective b.injective).mp he))
  · exact (map_mono hB).trans_eq (map_equiv_normalizer_eq Q b)
  · rw [show U = Q.map b.toMonoidHom from rfl,←map_equiv_normalizer_eq Q b,
      show D = B.map b.toMonoidHom from rfl,←map_equiv_normalizer_eq B b]
    exact map_mono hNB
  · rw [show D = B.map b.toMonoidHom from rfl,card_map_of_injective b.injective,
      Nat.card_congr (MulEquiv.ofBijective f ⟨hf,hs⟩).toEquiv]
    exact hfive
end BinaryLinear.QuinticNormalizer

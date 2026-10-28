module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.ConstrainedStar
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.QuotientRank
public import Theory.SpecificGroups.OddThreeRank

/-!
# Odd ternary containing components in 10.2.6

The original moved module survives modulo the central two-core of a
quasisimple containing component with order at least eight. Its two-core
quotient therefore has two-rank at least three. The concrete odd PSL₃ and
PSU₃ carriers have two-rank at most two, so neither can be that quotient.

For either strict member of the actual containing pair, the completed C.2.7
argument excludes the constrained case. Odd-core removal then supplies
quasisimplicity. Thus the literal pair applications need no distinctness,
cubic-divisor or model-recognition callback. They preserve the original
factor, exchanger and half-join. The remaining model rows and final assembly
belong to qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the independent
input of qt-d-10-nona5-point-selection, ultimately discharged by
qt-d-10-nona5-point-control.

Source: Aschbacher--Smith A.3.12(9) and 10.2.6, pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- The actual odd ternary model predicates have two-rank at most two. -/
theorem odd_three_model_twoRank_le {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL X 3 p ∨ ClassicalGroup.IsPSU X 3 p) :
    primeRank 2 X ≤ 2 := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,hc,⟨e⟩⟩
  · rw [primeRank_congr 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le hp ho hF
  · let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J hp ho hF hc

/-- The moved module excludes either odd ternary core quotient of a
quasisimple overgroup, independently of containing-component distinctness. -/
theorem not_odd_three_quasisimple_overgroup_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {s : G} {K : Subgroup G} [IsQuasisimple K]
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 p ∨
      ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 p) : False := by
  have hl := quasisimple_overgroup_quotient_twoRank D hBK
  have hu := odd_three_model_twoRank_le hp ho hm
  omega

/-- Odd-core removal and the completed constrained exclusion apply to the
first strict member with its original relative normality. -/
theorem ContainingPair.first_quasisimple_of_strict
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : L.subgroupOf H < K₁) : IsQuasisimple K₁ := by
  rcases C.first_component.component_or_generalizedFitting_eq_pCore
      (oddCore_eq_bot_of_moduleChoice hchoice hmany D hn hna C.half_le) with hq | hf
  · exact hq.2
  · exact (C.first_not_constrained_of_strict hchoice hmany hn hna hstrict hf).elim

/-- The same argument retains the actual opposite factor and exchanger. -/
theorem ContainingPair.second_quasisimple_of_strict
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : (L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂) :
    IsQuasisimple K₂ := by
  rcases C.second_component.component_or_generalizedFitting_eq_pCore
      (oddCore_eq_bot_of_moduleChoice hchoice hmany D hn hna C.half_le) with hq | hf
  · exact hq.2
  · exact (C.second_not_constrained_of_strict hchoice hmany hn hna hstrict hf).elim

/-- Exclude the first strict odd ternary containing quotient. -/
theorem ContainingPair.impossible_of_first_strict_odd_three_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : L.subgroupOf H < K₁)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (K₁ ⧸ pCore 2 K₁) 3 p ∨
      ClassicalGroup.IsPSU (K₁ ⧸ pCore 2 K₁) 3 p) : False := by
  let := C.first_quasisimple_of_strict hchoice hmany hn hna hstrict
  let K := K₁.map H.subtype
  let a := K₁.equivMapOfInjective H.subtype H.subtype_injective
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv a
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hLK : L.map (MulAut.conj (1 : G)).toMonoidHom ≤ K := by
    have hh := map_mono (f := H.subtype) C.first_le
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
    simpa only [hid,Subgroup.map_id,map_subgroupOf_eq_of_le C.left_le] using hh
  apply not_odd_three_quasisimple_overgroup_quotient D hLK hp ho
  rcases hm with hm | hm
  · exact .inl (hm.of_mulEquiv b.symm)
  · exact .inr (hm.of_mulEquiv b.symm)

/-- Exclude the second strict odd ternary containing quotient. -/
theorem ContainingPair.impossible_of_second_strict_odd_three_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : (L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (K₂ ⧸ pCore 2 K₂) 3 p ∨
      ClassicalGroup.IsPSU (K₂ ⧸ pCore 2 K₂) 3 p) : False := by
  let := C.second_quasisimple_of_strict hchoice hmany hn hna hstrict
  let K := K₂.map H.subtype
  let a := K₂.equivMapOfInjective H.subtype H.subtype_injective
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv a
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hLK : L.map (MulAut.conj t).toMonoidHom ≤ K := by
    simpa only [map_subgroupOf_eq_of_le C.right_le] using map_mono (f := H.subtype) C.second_le
  apply not_odd_three_quasisimple_overgroup_quotient D hLK hp ho
  rcases hm with hm | hm
  · exact .inl (hm.of_mulEquiv b.symm)
  · exact .inr (hm.of_mulEquiv b.symm)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness

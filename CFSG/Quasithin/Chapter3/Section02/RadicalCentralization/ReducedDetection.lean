module

public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Centralizing
public import Theory.GroupTheory.CentralPChiefFactors.Coprime

/-!
# Detection of a primary radical in its original Sylow join

If a two-perfect subgroup acts nontrivially on R₂ of an overgroup in
which it is subnormal, its intrinsic signalizer module is nontrivial.
A.4.11 detects that same intrinsic module inside its own Sylow join.
An odd-prime-group quotient supplies the chief-factor condition.
All maps below are the literal subgroup inclusions.
Source: Aschbacher--Smith A.4.8 and A.4.11, pp.59--61; used in 3.2.14.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter3.RadicalCentralization
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial reduced action detects the intrinsic module in the
original ambient group. -/
theorem intrinsicModule_ne_bot_of_reduced_action (X J : Subgroup G)
    (hXJ : X ≤ J) (hsub : (X.subgroupOf J).IsSubnormal)
    (hX : IsPPerfect 2 X)
    (hne : ⁅reducedTwoSubgroup J, X.subgroupOf J⁆ ≠ ⊥) :
    intrinsicSignalizerModule X ≠ ⊥ := by
  let e := subgroupOfEquivOfLe hXJ
  have hp : IsPPerfect 2 (X.subgroupOf J) :=
    hX.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hi : intrinsicSignalizerModule (X.subgroupOf J) ≠ ⊥ := by
    intro he
    exact hne (bot_unique ((reduced_commutator_le_intrinsicModule _ hsub hp).trans_eq he))
  intro he
  have hm := intrinsicSignalizerModule_map_of_injective J.subtype J.subtype_injective
    (X.subgroupOf J)
  rw [map_subgroupOf_eq_of_le hXJ,he] at hm
  exact hi ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp hm.symm)

/-- The nonzero intrinsic module is detected inside the original Sylow join. -/
theorem reduced_action_ne_bot_of_intrinsic_module (T : Subgroup G) (X : Subgroup G)
    (hT : T ≤ normalizer (X : Set G)) (hX : IsPPerfect 2 X)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hq : IsPGroup p (X ⧸ pCore 2 X))
    (hi : intrinsicSignalizerModule X ≠ ⊥) :
    ⁅reducedTwoSubgroup (X ⊔ T : Subgroup G), X.subgroupOf (X ⊔ T)⁆ ≠ ⊥ := by
  let Y := X.subgroupOf (X ⊔ T)
  let : Y.Normal := normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hT)
  let e : Y ≃* X := subgroupOfEquivOfLe (show X ≤ X ⊔ T from le_sup_left)
  let eq : (Y ⧸ pCore 2 Y) ≃* (X ⧸ pCore 2 X) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hc : HasCentralPChiefFactorsAbove 2 (pCore 2 Y) :=
    (hasCentralPChiefFactorsAbove_iff_quotient _).mpr
      (HasCentralPChiefFactors.of_isPGroup_of_ne (p := 2)
        (by intro he; rw [← he] at ho; norm_num at ho) (hq.of_equiv eq.symm))
  have hy : intrinsicSignalizerModule Y ≠ ⊥ := by
    intro he
    have hm := intrinsicSignalizerModule_map_of_injective (X ⊔ T).subtype
      (X ⊔ T).subtype_injective Y
    rw [map_subgroupOf_eq_of_le (show X ≤ X ⊔ T from le_sup_left),he,Subgroup.map_bot] at hm
    exact hi hm
  exact reduced_commutator_ne_bot_of_intrinsicModule_ne_bot Y
    (inferInstance : Y.Normal).isSubnormal
    (hX.of_surjective e.symm.toMonoidHom e.symm.surjective) hc hy

/-- The source primary radical is detected by R₂ of its own join with T,
using its original action in any subnormal overgroup. -/
theorem reduced_action_ne_bot_in_sylow_join (T : Subgroup G) (X J : Subgroup G)
    (hT : T ≤ normalizer (X : Set G)) (hXJ : X ≤ J)
    (hsub : (X.subgroupOf J).IsSubnormal) (hX : IsPPerfect 2 X)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hq : IsPGroup p (X ⧸ pCore 2 X))
    (hne : ⁅reducedTwoSubgroup J, X.subgroupOf J⁆ ≠ ⊥) :
    ⁅reducedTwoSubgroup (X ⊔ T : Subgroup G), X.subgroupOf (X ⊔ T)⁆ ≠ ⊥ :=
  reduced_action_ne_bot_of_intrinsic_module T X hT hX ho hq
    (intrinsicModule_ne_bot_of_reduced_action X J hXJ hsub hX hne)

end CFSG.Quasithin.Chapter3.RadicalCentralization

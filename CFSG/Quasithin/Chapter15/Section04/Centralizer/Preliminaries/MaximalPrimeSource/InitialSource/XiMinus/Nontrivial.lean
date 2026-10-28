module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.Setup
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
public import Theory.GroupTheory.CentralPChiefFactors.Coprime

/-!
# Nontriviality of the original Xi module

Faithful Xi membership gives a nonzero intrinsic module. Transport it along
the literal inclusion X ≤ J=XT, where X is normal and two-perfect. The odd
prime-group quotient X/O₂(X) has no two-chief factors, so the intrinsic
reduced-witness theorem proves [R₂(J),X] nontrivial. No universal A/C,
empty-family, ratio, or kernel hypothesis is required.
Source: Aschbacher--Smith, Lemma 3.2.13, printed pp.584--585, invoking A.4.11.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T X : Subgroup G}

/-- The original module [R₂(XT),X] is nontrivial for every faithful Xi member. -/
theorem sourceModule_ne_bot_of_mem_XiF (hX : X ∈ Chapter1.XiF G T) :
    sourceModule T X ≠ ⊥ := by
  let J := sourceGroup T X
  let Y := X.subgroupOf J
  let := hX.1.normal_in_join
  let e : Y ≃* X := subgroupOfEquivOfLe (show X ≤ J from le_sup_left)
  have hY : IsPPerfect 2 Y := hX.1.perfect.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hmap : Y.map J.subtype = X := map_subgroupOf_eq_of_le le_sup_left
  have hne : intrinsicSignalizerModule Y ≠ ⊥ := by
    intro he
    apply hX.2.2
    rw [← hmap, intrinsicSignalizerModule_map_of_injective J.subtype J.subtype_injective,
      he, Subgroup.map_bot]
  obtain ⟨p, hp, ho, hodd⟩ := hX.1.odd_quotient
  let : Fact p.Prime := ⟨hp⟩
  let eQ := QuotientGroup.congr (pCore 2 Y) (pCore 2 X) e (pCore_map_iso 2 e)
  have hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 Y) := by
    apply (hasCentralPChiefFactorsAbove_iff_quotient _).mpr
    exact HasCentralPChiefFactors.of_isPGroup_of_ne
      (by intro he; rw [← he] at ho; norm_num at ho)
      (hodd.isPGroup.of_equiv eQ.symm)
  exact reduced_commutator_ne_bot_of_intrinsicModule_ne_bot Y
    (show Y.Normal from inferInstance).isSubnormal hY hchief hne
end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus

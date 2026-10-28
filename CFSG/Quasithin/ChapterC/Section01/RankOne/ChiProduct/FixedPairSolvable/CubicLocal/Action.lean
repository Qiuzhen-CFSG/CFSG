module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.AbelianSylow
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Solvable
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicModule
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.CubicLocal
open ChapterB
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]

theorem abelian_sylow_action (ρ : Representation (ZMod 2) D W)
    (T : Sylow 2 D) (hP : IsMinimalParabolicOver T ⊤)
    (hsolv : Group.IsSolvable D) (hcore : pCore 2 D = ⊥)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ)
    (ha : IsMulCommutative T) :
    Nonempty (D ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨d,ht,_,hr,_⟩ := source_solvable_minimalParabolic_factors T hP hsolv hcore hf hff
  let a := d.toSolvableFFFactors
  have hc : a.count = 1 := a.count_eq_one_of_abelian_sylow_transitive T ha ht
  let e := MulEquiv.ofBijective (a.singleAmbientHom hc)
    ⟨a.singleAmbientHom_injective hf hcore hr hc,a.singleAmbientHom_surjective hc⟩
  obtain ⟨f⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact ⟨e.trans f⟩

variable {G : Type*} [Group G] [Finite G]
theorem reduced_abelian_sylow_action (T : Sylow 2 G)
    (hP : IsMinimalParabolicOver T ⊤) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hsolv : Group.IsSolvable (G ⧸ centralizer (U : Set G)))
    (ha : IsMulCommutative ((T : Subgroup G).map (QuotientGroup.mk' (centralizer (U : Set G))))) :
    Nonempty ((G ⧸ centralizer (U : Set G)) ≃* Equiv.Perm (Fin 3)) ∧
    Nat.card (G ⧸ centralizer (U : Set G)) = 6 ∧
    Nat.card (pResidual 2 (G ⧸ centralizer (U : Set G))) = 3 ∧
    Nat.card (⁅U,pResidual 2 G⁆ : Subgroup G) = 4 := by
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk := QuotientGroup.ker_mk' C
  let _ : IsMulCommutative U := IsElementaryAbelian.toIsMulCommutative 2
  let _ : CommGroup U := IsMulCommutative.instCommGroup
  let _ : Module.Finite (ZMod 2) (Additive U) := Module.Finite.of_finite
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hff : IsFFModule ρ := by
    obtain hh | hh := ChapterB.lemma_B_2_7 U q hq hk T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hh.1)).elim
    · exact hh.2.1
  have hc := hU.quotient_pCore_eq_bot
  have hn : q.ker ≠ ⊤ := by
    intro he
    have hCtop : C = ⊤ := hk.symm.trans he
    exact (hJ (by change elementaryAbelianMaxJ (T : Subgroup G) ≤ C; rw [hCtop]; exact le_top)).elim
  have hp := (minimalParabolic_reduced_image T hP q hq hc hn).2
  obtain ⟨e⟩ := abelian_sylow_action ρ (T.mapSurjective hq) hp hsolv hc
    (NormalElementaryQuotient.representation_injective U q hq hk) hff ha
  have h6 : Nat.card (G ⧸ C) = 6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    decide
  have h3 : Nat.card (pResidual 2 (G ⧸ C)) = 3 := by
    rw [←card_map_of_injective (f:=e.toMonoidHom) e.injective,
      map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,
      Equiv.Perm.twoResidual_eq_alternating,Nat.card_eq_fintype_card]
    decide +kernel
  exact ⟨⟨e⟩,h6,h3,FiveBlockSource.cubic_thompson_moved_card U q hq hk T hJ hsolv hc h6⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.CubicLocal

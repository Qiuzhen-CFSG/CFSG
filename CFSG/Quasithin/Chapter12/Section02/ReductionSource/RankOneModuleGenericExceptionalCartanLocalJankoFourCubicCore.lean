module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourCubicCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The chosen J₄ action and the original cubic fixed-core equality

Apply the fixed-core calculation to the original chosen-module input.
At an actual full-Sylow max4 marking, the original cubic fixes exactly the
certified normal eight inside the literal max4 two-core. The original map,
residual, both Hall products and S₅/S₃ quotient markings are retained.
The max1-kernel comparison and escaping-actor normalization remain to be
proved before this branch of the source theorem is closed.

Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.637,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The chosen original action yields the fixed-core equality for the same cubic. -/
theorem rankOne_local_cartan_jankoFour_native_cubic_fixed_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRC : residual H ≤ C.map Y.subtype)
    (e : (C ⧸ pCore 2 C) ≃* Janko4.Model) :
    ∃ (f : Y →* Janko4.Model) (S : Sylow 2 Janko4.Model),
      Function.Surjective f ∧
      (∀ x : C, f x = e (QuotientGroup.mk' (pCore 2 C) x)) ∧
      (S : Subgroup Janko4.Model) = ((T : Subgroup G).subgroupOf Y).map f ∧
      let R := ((residual H).subgroupOf Y).map f
      let D := (A.subgroupOf Y).map f
      let E := (B.subgroupOf Y).map f
      R ∈ ChapterA.Section03.localCComponents S ∧
      (S : Subgroup Janko4.Model) ≤ normalizer (R : Set Janko4.Model) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
      Nat.card B = 3 ∧ Nat.card E = 3 ∧ E ≤ R ∧
      IsCyclic D ∧ Odd (Nat.card D) ∧ E ≤ normalizer (D : Set Janko4.Model) ∧
      (D : Set Janko4.Model) * (S : Set Janko4.Model) =
        (S : Set Janko4.Model) * (D : Set Janko4.Model) ∧
      Group.IsSolvable ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) ∧
      (E : Set Janko4.Model) * (S : Set Janko4.Model) =
        (S : Set Janko4.Model) * (E : Set Janko4.Model) ∧
      Nat.card (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) = 3 * 2^21 ∧
      Nat.card (pCore 2 (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) = 2^20 ∧
      Nonempty (((R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) ⧸
        pCore 2 (R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) ≃*
        Equiv.Perm (Fin 5)) ∧
      (∃ e₃ : ((E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) ⧸
          pCore 2 (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) ≃*
          Equiv.Perm (Fin 3),
        let N := E ⊔ (S : Subgroup Janko4.Model)
        let q := e₃.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
        Nat.card (((S : Subgroup Janko4.Model).subgroupOf N).map q) = 2 ∧
        Nat.card ((E.subgroupOf N).map q) = 3) ∧
      ¬ D ≤ normalizer (R : Set Janko4.Model) ∧ ¬ D ≤ E ∧
      pCore 2 ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) ≠ ⊥ ∧
      LocalSieve.JankoFourWholeActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) ∧
      LocalSieve.JankoFourSolvableActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) ∧
      (∀ g : MulAut Janko4.Model,
        (S : Subgroup Janko4.Model).map g.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup →
        D.map g.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup →
        ¬ R.map g.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup) ∧
      pCore 2 R ≠ ⊥ ∧
      LocalSieve.JankoFourRemainingActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) ∧
      (∃ g : Janko4.Model,
        (S : Subgroup Janko4.Model).map (MulAut.conj g).toMonoidHom =
          Janko4.OuterReduction.OddIndex.twoSubgroup ∧
        ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E).map (MulAut.conj g).toMonoidHom ≤
          Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four ∧
        let I := (((((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E).map
          (MulAut.conj g).toMonoidHom).subgroupOf
          (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)).map
          Janko4.LocalStructure.MathieuHallActors.projection)
        Nat.card I = 9216 ∧
          ((∃ O : Sporadic.Mathieu.M24LocalGeometry.Octad,
            I ≤ Sporadic.Mathieu.M24LocalGeometry.octadStabilizer O) ∨
           ∃ t : Sporadic.Mathieu.M24,
            I ≤ Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.conjugateTrioStabilizer t)) ∧
      Nat.card D = 3 ∧ ⁅D,E⁆ = ⊥ ∧ Disjoint D E ∧
      Nat.card (D ⊔ E : Subgroup Janko4.Model) = 9 ∧
      IsElementaryAbelian 3 (D ⊔ E : Subgroup Janko4.Model) ∧
      Nat.card ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) = 9 * 2^21 ∧
      ∃ a : MulAut Janko4.Model,
        (S : Subgroup Janko4.Model).map a.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup ∧
        pCore 2 Janko4.LocalStructure.SymmetricLinear.max4Subgroup ⊓
          centralizer ((E.map a.toMonoidHom).subgroupOf
            Janko4.LocalStructure.SymmetricLinear.max4Subgroup :
              Set Janko4.LocalStructure.SymmetricLinear.max4Subgroup) =
            Janko4.LocalStructure.SymmetricLinear.NormalEight.eight :=
  LocalSieve.normal_jankoFour_native_cubic_fixed_core
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape hR C hC hRC e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

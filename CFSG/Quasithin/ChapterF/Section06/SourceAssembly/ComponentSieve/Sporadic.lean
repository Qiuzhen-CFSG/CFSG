module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.GroupTheory.SmallSylowObstructions
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount
public import Theory.SpecificGroups.Rudvalis.Model.Order

/-!
# Sporadic sieve for the small Sylow subgroup in F.6.17

Every named sporadic carrier in Theorem C, except the separately listed J₁,
has order divisible by sixteen. The Mathieu, J₂, HS and Ru cases use their
certified orders. For He and J₄, Lagrange's theorem applied to the actual
certified local subgroups suffices; the full group orders are unnecessary.
Consequently a Sylow two-subgroup of order at most eight leaves only J₁.

Source: Aschbacher--Smith, F.6.17, printed p.309, and the source Theorem C
sporadic list in A.2.4. The concrete carrier certificates cite their ATLAS data.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve

open CFSG.Quasithin.ClassificationModels
open CFSG.Quasithin.ChapterA.Section02

/-- The non-J₁ sporadic entries of source Theorem C all have a sixteen factor
in their actual carrier order. -/
theorem sixteen_dvd_sporadic_name (name : SporadicName) (hne : name ≠ .j3) :
    16 ∣ Nat.card name.Carrier := by
  cases name with
  | m11 =>
      change 16 ∣ Nat.card Sporadic.Mathieu.M11
      rw [Sporadic.Mathieu.m11_order]
      norm_num
  | m12 =>
      change 16 ∣ Nat.card Sporadic.Mathieu.M12
      rw [Sporadic.Mathieu.m12_order]
      norm_num
  | m22 =>
      change 16 ∣ Nat.card Sporadic.Mathieu.M22
      rw [Sporadic.Mathieu.m22_order]
      norm_num
  | m23 =>
      change 16 ∣ Nat.card Sporadic.Mathieu.M23
      rw [Sporadic.Mathieu.m23_order]
      norm_num
  | m24 =>
      change 16 ∣ Nat.card Sporadic.Mathieu.M24
      rw [Sporadic.Mathieu.m24_order]
      norm_num
  | j2 =>
      change 16 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier
      rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
      norm_num
  | j3 => exact (hne rfl).elim
  | j4 =>
      change 16 ∣ Nat.card Janko4.Model
      let hA := Janko4.matrixA_mul_self
      let hB := Janko4.matrixB_pow_four
      have hk := (Janko4.Cardinality.localKernel hA hB).card_subgroup_dvd_card
      rw [Janko4.Cardinality.localKernel_card hA hB] at hk
      exact (show 16 ∣ 2048 by norm_num).trans
        (hk.trans (Janko4.Cardinality.max1Subgroup hA hB).card_subgroup_dvd_card)
  | hs =>
      change 16 ∣ Nat.card Sporadic.LeechRelated.HS.Carrier
      rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
      norm_num
  | he =>
      change 16 ∣ Nat.card Held.He
      let K : Subgroup Held.He := Subgroup.closure
        (Set.range Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two.input)
      have hK : Nat.card K = 1024 :=
        Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two.order
      have hd := K.card_subgroup_dvd_card
      rw [hK] at hd
      exact (show 16 ∣ 1024 by norm_num).trans hd
  | ru =>
      change 16 ∣ Nat.card Rudvalis.Model
      rw [Rudvalis.model_card]
      norm_num

/-- Applying the actual source Theorem C sporadic list to the small Sylow
subgroup from F.6.17 leaves precisely the J₁ carrier. -/
theorem jankoOne_of_theoremC_sporadic_small_sylow
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hP : Nat.card P ≤ 8) (hmodel : IsTheoremCSporadicModel G) :
    Nonempty (G ≃* Janko1.Model) := by
  rcases hmodel with ⟨name, hne, ⟨e⟩⟩ | hJ
  · apply False.elim
    apply Theory.GroupTheory.not_sixteen_dvd_of_sylow_le_eight P hP
    rw [Nat.card_congr e.toEquiv]
    exact sixteen_dvd_sporadic_name name hne
  · exact hJ

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve

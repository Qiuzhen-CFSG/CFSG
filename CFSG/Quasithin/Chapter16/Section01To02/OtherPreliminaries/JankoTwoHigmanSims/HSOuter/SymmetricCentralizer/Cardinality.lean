module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer.GraphBound.Certificate

/-!
# The HS parity restriction halves the graph-centralizer bound

The original HS generators are even, whereas the specified outer involution
is odd. Multiplication by that involution gives a second, disjoint copy of the
HS centralizer inside its graph centralizer. The checked bound 80,640 therefore
gives 40,320 for the centralizer in the actual HS carrier.

Source: Aschbacher–Smith 16.1.5(10), p.1172; GLS3 Table 5.3m, class 2D.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer
open Sporadic.LeechRelated.HS OrderCertificate NormalizerIndex
open Subgroup GraphBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

local notation "C" => permutationCentralizer symmetricPermutation

private theorem generatorA_sign : Equiv.Perm.sign generatorA = 1 := by
  rw [← a_eq_generator]
  decide +kernel

private theorem generatorB_sign : Equiv.Perm.sign generatorB = 1 := by
  rw [← b_eq_generator]
  decide +kernel

private theorem generated_le_sign_ker : generated ≤ Equiv.Perm.sign.ker := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · exact generatorA_sign
  · exact (Set.mem_singleton_iff.mp hg) ▸ generatorB_sign

private theorem symmetric_sign : Equiv.Perm.sign symmetricPermutation = -1 := by
  decide +kernel

private theorem symmetric_mem_graphCentralizer : symmetricPermutation ∈ graphCentralizer := by
  constructor
  · change ∀ x y, adjacency (symmetricPermutation x) (symmetricPermutation y) ↔ adjacency x y
    apply allFin
    decide +kernel
  · exact mem_centralizer_singleton_iff.mpr rfl

private theorem inclusion_mem_graphCentralizer (g : C) : inclusion g.val ∈ graphCentralizer :=
  ⟨generated_le_graphGroup g.val.property, g.property⟩

private def pairMap (x : C × Bool) : graphCentralizer :=
  if x.2 then
    ⟨inclusion x.1.val * symmetricPermutation,
      graphCentralizer.mul_mem (inclusion_mem_graphCentralizer x.1)
        symmetric_mem_graphCentralizer⟩
  else ⟨inclusion x.1.val, inclusion_mem_graphCentralizer x.1⟩

private theorem pairMap_injective : Function.Injective pairMap := by
  rintro ⟨x, b⟩ ⟨y, c⟩ h
  have hv := congrArg Subtype.val h
  have hs := congrArg Equiv.Perm.sign hv
  have heven (z : C) : Equiv.Perm.sign (inclusion z.val) = 1 :=
    generated_le_sign_ker z.val.property
  have hbc : b = c := by
    cases b <;> cases c <;> try rfl
    all_goals
      simp only [pairMap, Bool.false_eq_true, if_false, if_true,
        map_mul, heven, symmetric_sign, one_mul] at hs
      norm_num at hs
  subst c
  apply Prod.ext
  · apply Subtype.ext
    apply Sporadic.LeechRelated.HS.inclusion_injective
    cases b
    · exact hv
    · exact mul_right_cancel hv
  · rfl

/-- The exact HS centralizer has order at most 8!. -/
theorem centralizer_card_le : Nat.card C ≤ 40320 := by
  have h := Nat.card_le_card_of_injective pairMap pairMap_injective
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
  have hb := GraphBound.Certificate.graphCentralizer_card_le
  omega

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer

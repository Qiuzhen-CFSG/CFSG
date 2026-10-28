module
public import Stellmacher.SectionOne.NineCoreSupportDecompositionCountingLines
public import Theory.GroupAction.IndependentCoprimeSupports
public import Theory.GroupAction.CoprimeCommutatorContainment
public import Theory.GroupAction.ActorSubtypeCommutator
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.NormalizedSupCard
/-!
# A small cubic support inside an elementary group of order nine

A faithful elementary abelian group of order nine moving a binary space of
order sixteen has a subgroup of order three moving only a plane. Restrict
to the actual support, count its two nontrivial character kernels, and
transport one complementary support back through the literal inclusions.
This excludes the elementary-nine alternative in the no-small-three branch
of Aschbacher–Smith D.2.26–29, pp.191–192.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
  [IsElementaryAbelian 2 V] [MulDistribMulAction G V] [FaithfulSMul G V]

theorem exists_small_three_support_of_nine
    (A : Subgroup G) [IsElementaryAbelian 3 A] (hA : Nat.card A = 9)
    (hV : Nat.card (commutatorAction A V) = 16) :
    ∃ X : Subgroup G, X ≤ A ∧ Nat.card X = 3 ∧ Nat.card (commutatorAction X V) = 4 := by
  let U := commutatorAction A V
  let : IsInvariant A V U := commutatorAction_isInvariant
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective U.subtype U.subtype_injective
  let : IsElementaryAbelian 3 (⊤ : Subgroup A) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup A).subtype Subtype.val_injective
  obtain ⟨m,hm⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    rw [hA,hm]
    exact (by decide : Nat.Coprime 9 2).pow_right m
  have hf : fixingSubgroup A (Set.univ : Set U) = ⊥ := by
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    apply ActionSupport.eq_one_of_fixes_support A hcop a
    intro v hv
    exact congrArg Subtype.val (((mem_fixingSubgroup_iff (M := A)).mp ha) ⟨v,hv⟩ trivial)
  have hn := Stellmacher.SectionOne.nineCoreSupportDecomposition_supporting_lines_card
    (⊤ : Subgroup A) inferInstance (by simpa using hA) hV hf
  have hex : Nonempty {X : Subgroup A // X ≤ ⊤ ∧ Nat.card X = 3 ∧
      Nat.card (FixedPoints.subgroup X U) = 4} := by
    exact (Nat.card_pos_iff.mp (by rw [hn]; decide)).1
  obtain ⟨⟨X,hX⟩⟩ := hex
  let : IsInvariant X V U := ⟨fun x v => IsInvariant.invariant (A := A) (x : A) v⟩
  have hcopX : Nat.Coprime (Nat.card X) (Nat.card V) := by
    rw [hX.2.1,hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hcopU : Nat.Coprime (Nat.card X) (Nat.card U) := by
    rw [hX.2.1,hV]
    decide
  have hc := ActionSupport.fixed_support_isCompl (G := A) (V := U) X hcopU
  have hfour : Nat.card (commutatorAction X U) = 4 := by
    have hn : commutatorAction X U ≤ normalizer (FixedPoints.subgroup X U : Set U) := by
      rw [normalizer_eq_top_iff.mpr (normal_of_isMulCommutative _)]
      exact le_top
    have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes
      (FixedPoints.subgroup X U) (commutatorAction X U) hn
    rw [hc.inf_eq_bot,hc.sup_eq_top,card_bot,card_top,hX.2.2,one_mul,hV] at hm
    omega
  have hcontain : commutatorAction X V ≤ U := by
    rw [commutatorAction_eq_closure]
    apply (closure_le (K := U)).mpr
    rintro _ ⟨x,v,rfl⟩
    change v⁻¹ * ((x : A) • v) ∈ commutatorAction A V
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨(x : A),v,rfl⟩
  have he := commutatorAction_map_eq_of_coprime_of_le U
    (Group.isSolvable_of_comm fun x y : V => mul_comm x y) hcopX hcontain
  refine ⟨X.map A.subtype,map_subtype_le X,?_,?_⟩
  · rw [card_map_of_injective A.subtype_injective]
    exact hX.2.1
  · rw [commutatorAction_map_actor_subtype,← he,card_map_of_injective U.subtype_injective]
    exact hfour

end CFSG.Quasithin.ChapterD.CyclicSource

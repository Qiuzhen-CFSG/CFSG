module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.CubicModule
public import Theory.SpecificGroups.Alternating.FourMovedCubic
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CoprimeQuotientSubgroups.PrimeLift

/-!
# The cubic A₄ residual in an ordinary A₇ block extension

The ambient two-core commutator is contained in the block's intrinsic
moving layer by subnormal two-perfectness. Coprime idempotence makes the
two commutators equal. The literal three-cycle therefore has a four-element
moving subgroup even in the ambient core. Lifting its cubic subgroup through
the actual core quotient constructs an A₄ two-residual in the ambient join.

Source: Y = O²(Y₀) in C.1.29, printed p.134.
-/
public section
open Subgroup
open BinaryPermutation.SevenCubic
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LocalC129
variable {G : Type*} [Group G] [Finite G]

theorem ambient_cubic_moving_card {K : Subgroup G} (hK : IsBlock K)
    (rho : alternatingGroup (Fin 7) →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 7))))
    (model : BlockModuleModel K rho)
    (hact : ∀ (g : alternatingGroup (Fin 7)) (v : Multiplicative (BinaryPermutation.natural (Fin 7))),
      (rho g v).toAdd = BinaryPermutation.naturalRepresentation (Fin 7) g.val v.toAdd)
    (X : Subgroup K) (hX : Nat.card X = 3)
    (himage : X.map ((alternatingGroup (Fin 7)).subtype.comp
      (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) = C) :
    Nat.card (⁅pCore 2 G, X.map K.subtype⁆ : Subgroup G) = 4 := by
  let U := (blockU K).map K.subtype
  let A := X.map K.subtype
  have hA : Nat.card A = 3 := (card_map_of_injective K.subtype_injective).trans hX
  have hU : U ≤ pCore 2 G := (map_mono blockU_le_core).trans
    (pCoreIn_le_of_subnormal 2 hK.subnormal)
  have hm : ⁅pCore 2 G, A⁆ ≤ U :=
    (commutator_mono le_rfl (map_subtype_le X)).trans
      (commutator_le_core_commutator_of_isSubnormal K (pCore 2 G)
        hK.subnormal hK.short.twoPerfect pCore_isPGroup le_normalizer_of_normal)
  have hc : Nat.Coprime (Nat.card A) (Nat.card (pCore 2 G)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hA, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  rw [commutator_eq_of_coprime_containment (pCore 2 G) U A
    le_normalizer_of_normal hc hU hm]
  change Nat.card (⁅(blockU K).map K.subtype, X.map K.subtype⁆ : Subgroup G) = 4
  rw [← map_commutator, card_map_of_injective K.subtype_injective]
  exact cubic_moving_card_of_model hK.short rho model hact X hX himage
/-- The required cubic complement and A₄ residual exist in the actual
ambient two-core extension of the marked ordinary A₇ block. -/
theorem exists_cubic_residual_of_model {K : Subgroup G} (hK : IsBlock K)
    (rho : alternatingGroup (Fin 7) →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 7))))
    (model : BlockModuleModel K rho)
    (hact : ∀ (g : alternatingGroup (Fin 7)) (v : Multiplicative (BinaryPermutation.natural (Fin 7))),
      (rho g v).toAdd = BinaryPermutation.naturalRepresentation (Fin 7) g.val v.toAdd) :
    ∃ X : Subgroup K, Nat.card X = 3 ∧
      X.map ((alternatingGroup (Fin 7)).subtype.comp
        (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) = C ∧
      Nonempty (pResidual 2 (pCore 2 G ⊔ X.map K.subtype : Subgroup G) ≃*
        alternatingGroup (Fin 4)) := by
  let q : K →* alternatingGroup (Fin 7) :=
    model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := model.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    ext x
    change model.quotientIso (QuotientGroup.mk' (pCore 2 K) x) = 1 ↔ x ∈ pCore 2 K
    rw [model.quotientIso.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hc : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hk, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hCA : C ≤ alternatingGroup (Fin 7) := by
    apply zpowers_le.mpr
    change Equiv.Perm.sign cycle = 1
    decide
  let D := C.subgroupOf (alternatingGroup (Fin 7))
  have hD : Nat.card D = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCA).toEquiv).trans card_actor
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨X, hX, ⟨eX⟩⟩ := exists_prime_subgroup_equiv_of_surjective_coprime q hq hc D
    (IsPGroup.of_card (n := 1) (by simpa using hD))
  have hXcard : Nat.card X = 3 := (Nat.card_congr eX.toEquiv).trans hD
  have hXm : X.map ((alternatingGroup (Fin 7)).subtype.comp q) = C := by
    rw [← map_map, hX, map_subgroupOf_eq_of_le hCA]
  refine ⟨X, hXcard, hXm, ?_⟩
  exact AlternatingFourTransitiveCubic.residual_join_equiv_of_commutator_four
    (pCore 2 G) (X.map K.subtype) pCore_isPGroup
    ((card_map_of_injective K.subtype_injective).trans hXcard)
    (ambient_cubic_moving_card hK rho model hact X hXcard hXm)
end CFSG.Quasithin.ChapterC.LocalC129


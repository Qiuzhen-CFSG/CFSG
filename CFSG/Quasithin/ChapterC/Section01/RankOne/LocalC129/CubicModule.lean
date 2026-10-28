module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.BinaryPermutation.SevenCubic
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The cubic moving space in the prescribed A₇ block module

The three-cycle on the last three coordinates moves a two-dimensional binary
space. Coprime splitting transports this space through the actual quotient
U(L) → U(L)/C_U(L), retaining any central fixed layer. The resulting literal
subgroup commutator has order four, as needed for Y = O²(Y₀) in C.1.29, p.134.
-/
public section
namespace CFSG.Quasithin.ChapterC.LocalC129
open Subgroup
open BinaryPermutation.SevenCubic
variable {L : Type*} [Group L] [Finite L]

/-- The literal cubic complement moves exactly a four-group in U(L), even
when the block has a nontrivial central fixed layer. -/
theorem cubic_moving_card_of_model
    (h : IsShort L)
    (rho : alternatingGroup (Fin 7) →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 7))))
    (model : BlockModuleModel L rho)
    (hact : ∀ (g : alternatingGroup (Fin 7)) (v : Multiplicative (BinaryPermutation.natural (Fin 7))),
      (rho g v).toAdd = BinaryPermutation.naturalRepresentation (Fin 7) g.val v.toAdd)
    (X : Subgroup L) (hX : Nat.card X = 3)
    (himage : X.map ((alternatingGroup (Fin 7)).subtype.comp
      (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) = C) :
    Nat.card (⁅blockU L, X⁆ : Subgroup L) = 4 := by
  let U := blockU L
  let : IsElementaryAbelian 2 U := h.elementary
  let q := (alternatingGroup (Fin 7)).subtype.comp
    (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  let a : X →* C := (MulEquiv.subgroupCongr himage).toMonoidHom.comp (q.subgroupMap X)
  have ha : Function.Surjective a :=
    (MulEquiv.subgroupCongr himage).surjective.comp (q.subgroupMap_surjective X)
  let : Normalizes X U := ⟨le_normalizer_of_normal⟩
  let : MulDistribMulAction X U := conjMulDistribMulActionOfLeNormalizer X U le_normalizer_of_normal
  let f : U →* NaturalV := model.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed L))
  have hf : Function.Surjective f := model.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have he (x : X) (u : U) : f (x • u) = (a x) • f u := by
    change model.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L x u)) = _
    rw [model.intertwining]
    apply Multiplicative.toAdd.injective
    rw [hact]
    rfl
  have hcop : Nat.Coprime (Nat.card X) (Nat.card U) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
    rw [hX, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hk : f.ker ≤ FixedPoints.subgroup X U := by
    intro u hu x
    have huZ : u ∈ blockFixed L := by
      apply (QuotientGroup.eq_one_iff u).mp
      exact model.moduleIso.map_eq_one_iff.mp hu
    apply Subtype.ext
    change (x : L) * (u : L) * (x : L)⁻¹ = u
    have hc : (x : L) * (u : L) = (u : L) * (x : L) := mem_center_iff.mp huZ x
    rw [hc, mul_inv_cancel_right]
  let _ := MulDistribMulAction.compHom NaturalV a
  let e := Theory.GroupAction.movingEquivOfFixedKernel f hf he hcop hk
  have hm : Nat.card (commutatorAction X U) = 4 := by
    rw [Nat.card_congr e.toEquiv,
      Theory.GroupAction.commutatorAction_eq_of_actor_surjective a ha]
    exact card_moving_natural
  rw [← commutatorAction_subgroup_conj_map_eq_commutator U X le_normalizer_of_normal,
    card_map_of_injective U.subtype_injective]
  exact hm
end CFSG.Quasithin.ChapterC.LocalC129

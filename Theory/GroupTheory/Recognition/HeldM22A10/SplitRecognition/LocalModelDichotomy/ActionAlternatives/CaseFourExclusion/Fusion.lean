module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.Ambient
public import Theory.GroupTheory.InvolutionTransfer
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The final Case IV fusion contradiction

Thompson transfer fuses d into H = E<a,b>. Every involution there has a
centralizer of order at least 32 in the coordinate Sylow subgroup. Conjugation
embeds this two-subgroup in the ambient centralizer of d, contradicting a
Sylow order of sixteen. The no-index-two input follows from simplicity and
the actual involution-centralizer order 384.

The Sylow-centralizer order is an explicit remaining source premise, not an
assertion established by this module. Its producer must supply it before
this conditional result excludes Case IV.
Source: Janko, J. Algebra 9 (1968), Section 1, printed p.3.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour
open Subgroup
universe u

private theorem H_index : H.index = 2 := by
  have hh := H.index_mul_card
  rw [H_card, model_card] at hh
  omega

private theorem d_order : orderOf d = 2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

private theorem centralizer_card_lower (x : Model) (hx : x ∈ H) (hsq : x*x=1) :
    32 ≤ Nat.card (centralizer ({x} : Set Model)) := by
  let : DecidablePred (· ∈ centralizer ({x} : Set Model)) := fun y =>
    decidable_of_iff (y*x=x*y) mem_centralizer_singleton_iff.symm
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [mem_centralizer_singleton_iff] using centralizer_bound x hx hsq

variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K)
  (R : JankoCoordinates (D.binaryAction K hK) .four)

-- Conjugation embeds the model centralizer in the ambient centralizer of d.
private theorem conjugate_centralizer_card_le
    (hcard : ∀ P : Sylow 2 (centralizer ({into D K hK R d} : Set G)), Nat.card P = 16)
    (x : Model) (hconj : IsConj (into D K hK R d) (into D K hK R x)) :
    Nat.card (centralizer ({x} : Set Model)) ≤ 16 := by
  classical
  obtain ⟨g,hg⟩ := isConj_iff.mp hconj.symm
  let f : Model →* G := (MulAut.conj g).toMonoidHom.comp (into D K hK R)
  have hf : Function.Injective f := (MulAut.conj g).injective.comp (into_injective D K hK R)
  have hfx : f x = into D K hK R d := hg
  let Cx := centralizer ({x} : Set Model)
  let Cd := centralizer ({into D K hK R d} : Set G)
  let fc : Cx →* Cd := (f.comp Cx.subtype).codRestrict Cd (by
    intro y
    apply mem_centralizer_singleton_iff.mpr
    change f y * into D K hK R d = into D K hK R d * f y
    rw [← hfx, ← map_mul, ← map_mul]
    exact congrArg f (mem_centralizer_singleton_iff.mp y.property))
  have hfc : Function.Injective fc := by
    intro y z h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  have hp : IsPGroup 2 Model := IsPGroup.of_card (model_card.trans (by decide : 128 = 2^7))
  obtain ⟨P,hP⟩ := ((hp.to_subgroup Cx).of_surjective fc.rangeRestrict fc.rangeRestrict_surjective).exists_le_sylow
  have hle := Nat.card_le_card_of_injective _ (inclusion_injective hP)
  rw [hcard P] at hle
  exact (Nat.card_congr (MonoidHom.ofInjective hfc).toEquiv).le.trans hle

variable [IsSimpleGroup G]

private theorem no_normal_index_two (D : LocalData G) (N : Subgroup G) (hN : N.Normal) : N.index ≠ 2 := by
  rcases hN.eq_bot_or_eq_top with rfl | rfl
  · rw [index_bot]
    have hbound : 384 ≤ Nat.card G := by
      rw [← D.centralizer_card]
      exact Nat.card_le_card_of_injective _ D.centralizer.subtype_injective
    omega
  · simp

/-- The final transfer contradiction once the source Sylow-centralizer step is supplied. -/
public theorem false_of_sylowCentralizer_card
    (hcard : ∀ P : Sylow 2 (centralizer ({into D K hK R d} : Set G)), Nat.card P = 16) :
    False := by
  classical
  let e := modelEquivSylow D K hK R
  let U := H.map e.toMonoidHom
  have hU : U.index = 2 := (index_map_equiv H e).trans H_index
  have heorder : orderOf (e d) = 2 := (e.orderOf_eq d).trans d_order
  obtain ⟨u,hu,huU⟩ := (sylow D K hK R).exists_isConj_mem_of_index_two
    (no_normal_index_two D) U hU (e d) heorder
  obtain ⟨x,hx,hxu⟩ := huU
  have hu' : IsConj (into D K hK R d) (into D K hK R x) := by
    change IsConj (into D K hK R d) (u : G) at hu
    rw [← hxu] at hu
    exact hu
  have hsq : x*x=1 := by
    apply into_injective D K hK R
    rw [map_mul, map_one]
    have hp := hu'.pow 2
    have hd : into D K hK R d ^ 2 = 1 := by
      rw [← map_pow, show d ^ 2 = 1 by decide +kernel, map_one]
    rw [hd] at hp
    simpa only [pow_two] using isConj_one_right.mp hp
  have hlo := centralizer_card_lower x hx hsq
  have hhi := conjugate_centralizer_card_le D K hK R hcard x hu'
  omega

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour

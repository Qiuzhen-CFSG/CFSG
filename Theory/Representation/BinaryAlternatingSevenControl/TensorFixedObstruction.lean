module
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer
public import Theory.Representation.BinaryPermutation.SevenParabolic.Ranks
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry.Coordinates

/-!
# Sylow fixed-space obstructions for the two binary A₇ models

In a faithful four-dimensional action the Sylow fixed-line stabilizer has
order 168. A normal A₇ actor is the whole faithful actor, so this also
controls Sylow subgroups of the full group. For the deleted seven-letter
module, a full Sylow subgroup of S₇ fixes an even vector of weight four.
Its stabilizer embeds in S₄ × S₃, whose order is prime to five. Thus neither
fixed-space centralizer contains a subgroup with an A₅ section.

The permutation proof checks only sixteen explicit Sylow words; restriction
to the support and its complement gives the stabilizer bound structurally.
Source application: Aschbacher–Smith 9.3.1 and 9.3.7, combined manuscript
(1 March 2004), printed pp.733–734, and the binary A₇ models of B.5.1.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryAlternatingSevenControl
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem sylow_fixedKernel_card (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (R : Sylow 2 A7) : Nat.card (subspaceKernel ρ (fixedSpace ρ R) ⊤) = 168 := by
  have h := (subspaceKernel ρ (fixedSpace ρ R) ⊤).card_mul_index
  have hc : Nat.card A7 = 2520 := by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  rw [sylow_fixedKernel_index ρ hf hd R, hc] at h
  omega

theorem sylow_fixedKernel_five_free (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (R : Sylow 2 A7) (B : Subgroup A7)
    (hB : ∀ b ∈ B, ∀ v ∈ fixedSpace ρ R, ρ b v = v) : ¬5 ∣ Nat.card B := by
  have hle : B ≤ subspaceKernel ρ (fixedSpace ρ R) ⊤ := fun b hb => ⟨mem_top b,hB b hb⟩
  have hc := card_dvd_of_le hle
  rw [sylow_fixedKernel_card ρ hf hd R] at hc
  exact fun h => (by decide : ¬5 ∣ 168) (h.trans hc)

theorem normal_actor_sylow_fixedKernel_five_free
    {D : Type*} [Group D] [Finite D]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 4)
    (N : Subgroup D) [N.Normal] (eN : N ≃* A7)
    (P : Sylow 2 D) (B : Subgroup D)
    (hB : ∀ b ∈ B, ∀ v ∈ fixedSpace ρ P, ρ b v = v) : ¬5 ∣ Nat.card B := by
  have hN : N = ⊤ := normal_alternatingSeven_eq_top ρ hf hd N eN
  let e : D ≃* A7 := topEquiv.symm.trans ((MulEquiv.subgroupCongr hN.symm).trans eN)
  let σ : Representation (ZMod 2) A7 V := ρ.comp e.symm.toMonoidHom
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have h := sylow_fixedKernel_five_free σ (hf.comp e.symm.injective) hd R
    (B.map e.toMonoidHom) (by
      rintro _ ⟨b,hb,rfl⟩ v hv
      change ρ (e.symm (e b)) v = v
      rw [e.symm_apply_apply]
      apply hB b hb
      intro p
      have hh := hv ⟨e p.val,mem_map_of_mem e.toMonoidHom p.property⟩
      change ρ (e.symm (e p.val)) v = v at hh
      change ρ p.val v = v
      simpa only [e.symm_apply_apply] using hh)
  rw [card_map_of_injective e.injective] at h
  exact h

end Representation.BinaryAlternatingSevenControl

namespace BinaryPermutation.SevenSylowFixed
open SevenParabolic Representation.AlternatingSevenConjugatePair.ElementaryGeometry

private theorem firstFour_support (i : Fin 7) : firstFour.val i ≠ 0 ↔ i.val < 4 := by
  fin_cases i <;> decide

private def blockRestriction : pointStabilizer firstFour →*
    Equiv.Perm {i : Fin 7 // i.val < 4} × Equiv.Perm {i : Fin 7 // ¬ i.val < 4} where
  toFun g := ⟨g.val.subtypePerm (fun i => by
      simpa only [← firstFour_support] using support_invariant firstFour g i),
    g.val.subtypePerm (fun i => by
      simpa only [← firstFour_support] using not_congr (support_invariant firstFour g i))⟩
  map_one' := by ext i <;> rfl
  map_mul' _ _ := by ext i <;> rfl

private theorem blockRestriction_injective : Function.Injective blockRestriction := by
  intro g h he
  apply Subtype.ext
  apply Equiv.ext
  intro i
  by_cases hi : i.val < 4
  · exact congrArg Subtype.val (Equiv.congr_fun (congrArg Prod.fst he) ⟨i,hi⟩)
  · exact congrArg Subtype.val (Equiv.congr_fun (congrArg Prod.snd he) ⟨i,hi⟩)

private theorem firstFour_stabilizer_card_dvd : Nat.card (pointStabilizer firstFour) ∣ 144 := by
  have h := card_dvd_of_injective blockRestriction blockRestriction_injective
  have h4 : Fintype.card {i : Fin 7 // i.val < 4} = 4 := by decide
  have h3 : Fintype.card {i : Fin 7 // ¬i.val < 4} = 3 := by decide
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm, h4, h3,
    Nat.factorial] using h

private def conjugatePointStabilizer (g : Equiv.Perm (Fin 7)) (v : Space) :
    pointStabilizer v →* pointStabilizer (action g v) :=
  ((MulAut.conj g).toMonoidHom.comp (pointStabilizer v).subtype).codRestrict _ (by
    intro a
    change action (g * a.val * g⁻¹) (action g v) = action g v
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      action.inv_self_apply, a.property])

theorem weight_four_stabilizer_card_dvd (v : Space) (hv : weight v = 4) :
    Nat.card (pointStabilizer v) ∣ 144 := by
  obtain ⟨g,hg⟩ := exists_permutation_firstFour v hv
  have hi : Function.Injective (conjugatePointStabilizer g v) := by
    intro a b hab
    exact Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val hab))
  have hd := card_dvd_of_injective (conjugatePointStabilizer g v) hi
  rw [hg] at hd
  exact hd.trans firstFour_stabilizer_card_dvd

private noncomputable def standardSylow : Sylow 2 S7 :=
  (IsPGroup.of_card (show Nat.card sylowTwo = 2 ^ 4 by rw [sylowTwo_card]; decide)).toSylow (by
    have hh := sylowTwo.card_mul_index
    have hc : Nat.card S7 = 5040 := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [sylowTwo_card,hc] at hh
    have hi : sylowTwo.index = 315 := by omega
    rw [hi]
    decide)

private theorem standard_fixed : firstFour ∈ fixedSpace action sylowTwo := by
  rintro ⟨g,⟨w,rfl⟩⟩
  exact (by decide +kernel : ∀ w : Quadruple, action (word w) firstFour = firstFour) w

theorem exists_weight_four_sylow_fixed (P : Sylow 2 S7) :
    ∃ v : Space, weight v = 4 ∧ v ∈ fixedSpace action P := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S7 P standardSylow
  refine ⟨action g⁻¹ firstFour, (weight_permute _ _).trans firstFour_weight, ?_⟩
  intro p
  have hp : g * p.val * g⁻¹ ∈ sylowTwo := by
    have hh : g * p.val * g⁻¹ ∈ (g • P : Sylow 2 S7) := ⟨p.val,p.property,rfl⟩
    rw [hg] at hh
    exact hh
  have hf := standard_fixed ⟨g*p.val*g⁻¹,hp⟩
  change action (g * p.val * g⁻¹) firstFour = firstFour at hf
  have h := congrArg (action g⁻¹) hf
  change action p.val (action g⁻¹ firstFour) = action g⁻¹ firstFour
  simpa only [map_mul, Module.End.mul_apply, action.inv_self_apply] using h

theorem sylow_fixedKernel_five_free (P : Sylow 2 S7) (B : Subgroup S7)
    (hB : ∀ b ∈ B, ∀ v ∈ fixedSpace action P, action b v = v) : ¬5 ∣ Nat.card B := by
  obtain ⟨v,hv,hfix⟩ := exists_weight_four_sylow_fixed P
  have hle : B ≤ pointStabilizer v := fun b hb => hB b hb v hfix
  have hd := (card_dvd_of_le hle).trans (weight_four_stabilizer_card_dvd v hv)
  exact fun h => (by decide : ¬5 ∣ 144) (h.trans hd)

theorem natural_sylow_fixedKernel_five_free (P : Sylow 2 S7) (B : Subgroup S7)
    (hB : ∀ b ∈ B, ∀ v ∈ fixedSpace (naturalRepresentation (Fin 7)) P,
      naturalRepresentation (Fin 7) b v = v) : ¬5 ∣ Nat.card B := by
  apply sylow_fixedKernel_five_free P B
  intro b hb v hv
  let e := coreEquivNatural (Fin 7) (by decide)
  apply e.injective
  rw [coreEquivNatural_equivariant]
  apply hB b hb
  intro p
  change naturalRepresentation (Fin 7) p.val (e v) = e v
  exact (coreEquivNatural_equivariant (Fin 7) (by decide) p.val v).symm.trans
    (congrArg e (hv p))
end BinaryPermutation.SevenSylowFixed

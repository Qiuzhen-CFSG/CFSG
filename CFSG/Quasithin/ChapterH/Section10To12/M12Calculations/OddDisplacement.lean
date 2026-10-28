module

public import CFSG.Quasithin.ChapterH.Section10To12.Defs
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryPermutation.OrbitFixedSpace
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.Averaging
public import Theory.Mathieu.M12.Properties.Transitivity
public import Theory.GroupTheory.SharpSetStabilizer
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Odd-prime displacement on the native M₁₂ heart

For an odd-prime actor, the full twelve-letter permutation has at most four
fixed letters by sharp five-transitivity.  The prime-order orbit formula then
gives at most six orbits.  For an odd-order actor the natural heart has the
same fixed codimension as the full permutation module, so its displacement is
at least six.

This is the native even-core image modulo constants used in H.11.1, rather
than the eleven-dimensional deleted module.  Source: Aschbacher--Smith,
*The Classification of Quasithin Groups*, H.11, printed p.392 (PDF p.403).
-/

@[expose] public section

open Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations

private theorem m12_fixedPoints_card_le_four (x : Sporadic.Mathieu.M12)
    (hx : x ≠ 1) :
    Nat.card (Function.fixedPoints (x : Equiv.Perm (Fin 12))) ≤ 4 := by
  have hlt := Sporadic.Mathieu.m12_isSharplyFivePretransitive.card_fixedPoints_lt hx
  have hlt' :
      (Function.fixedPoints (x : Equiv.Perm (Fin 12))).ncard < 5 := by
    change ({a : Fin 12 | (x : Equiv.Perm (Fin 12)) a = a}).ncard < 5
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
    change (Finset.univ.filter (fun a : Fin 12 =>
      (x : Equiv.Perm (Fin 12)) a = a)).card < 5 at hlt
    exact hlt
  exact Nat.le_pred_of_lt hlt'

private theorem m12_prime_order_orbits_le_six (x : Sporadic.Mathieu.M12)
    (hp : (orderOf x).Prime) (ho : orderOf x ≠ 2) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (x : Equiv.Perm (Fin 12)))
      (Fin 12)) ≤ 6 := by
  let σ : Equiv.Perm (Fin 12) := x
  have hx : x ≠ 1 := by
    intro h
    apply hp.ne_one
    rw [h]
    exact orderOf_one
  have hfixed : Nat.card (Function.fixedPoints σ) ≤ 4 := by
    simpa only [σ] using m12_fixedPoints_card_le_four x hx
  have horder : orderOf σ = orderOf x := Subgroup.orderOf_coe x
  have hprimeσ : (orderOf σ).Prime := horder ▸ hp
  have hformula := Representation.primeOrder_perm_fixedPoints_orbit_formula
    (X := Fin 12) σ hprimeσ
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hprimeσ
  have hsum := Equiv.Perm.sum_cycleType_le σ
  rw [hn, Multiset.sum_replicate] at hsum
  have hsum' : (n + 1) * orderOf σ ≤ 12 := by
    simpa only [nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] using hsum
  have hpn : orderOf σ ≤ (n + 1) * orderOf σ :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
  have hp12 : orderOf σ ≤ 12 := by
    calc
      orderOf σ ≤ (n + 1) * orderOf σ := hpn
      _ ≤ 12 := hsum'
  have hp12' : orderOf x ≤ 12 := horder ▸ hp12
  have hne : 1 < orderOf x := hp.one_lt
  have hodd : Odd (orderOf x) := hp.odd_of_ne_two ho
  have hoddσ : Odd (orderOf σ) := horder ▸ hodd
  have horbit :
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) (Fin 12)) ≤ 6 := by
    rw [Nat.card_fin] at hformula
    interval_cases hpo : orderOf σ <;> omega
  simpa only [σ] using horbit

private theorem m12_natural_fixedCodim_eq_full_of_odd
    (A : Subgroup (Equiv.Perm (Fin 12))) (ho : Odd (Nat.card A)) :
    fixedCodim (BinaryPermutation.naturalRepresentation (Fin 12)) A =
      fixedCodim (BinaryPermutation.representation (Fin 12)) A := by
  let full := BinaryPermutation.representation (Fin 12)
  let core := BinaryPermutation.coreRepresentation (Fin 12)
  let natural := BinaryPermutation.naturalRepresentation (Fin 12)
  let trivial : Representation (ZMod 2) (Equiv.Perm (Fin 12)) (ZMod 2) :=
    Representation.trivial (ZMod 2) (Equiv.Perm (Fin 12)) (ZMod 2)
  have haug : ∀ g v, BinaryPermutation.augmentation (Fin 12) (full g v) =
      trivial g (BinaryPermutation.augmentation (Fin 12) v) := by
    intro g v
    simp [full, trivial, BinaryPermutation.augmentation_permute]
  have hfull := Representation.BinaryOffender.finrank_fixedSpace_surjection_of_odd
    full trivial (BinaryPermutation.augmentation (Fin 12)) haug
    (BinaryPermutation.augmentation_surjective (Fin 12)) A ho
  let I := LinearMap.ker (BinaryPermutation.augmentation (Fin 12)) ⊓
    Representation.BinaryOffender.fixedSpace full A
  let e : I ≃ₗ[ZMod 2]
      Representation.BinaryOffender.fixedSpace core A :=
    { toFun := fun v =>
        ⟨⟨v.val, v.property.1⟩,
          (BinaryPermutation.mem_core_fixedSpace_iff A _).mpr
            ((BinaryPermutation.mem_full_fixedSpace_iff A _).mp v.property.2)⟩
      invFun := fun v =>
        ⟨v.val.val,
          ⟨v.val.property,
            (BinaryPermutation.mem_full_fixedSpace_iff A _).mpr
              ((BinaryPermutation.mem_core_fixedSpace_iff A _).mp v.property)⟩⟩
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  have htrivial : Module.finrank (ZMod 2)
      (Representation.BinaryOffender.fixedSpace trivial A) = 1 := by
    have heq : Representation.BinaryOffender.fixedSpace trivial A = ⊤ := by
      apply top_unique
      intro v _ a
      simp [trivial]
    rw [heq, finrank_top]
    simp
  have heqfin : Module.finrank (ZMod 2) I =
      Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace core A) :=
    e.finrank_eq
  rw [htrivial, heqfin] at hfull
  have hnat := Representation.BinaryOffender.finrank_fixedSpace_surjection_of_odd
    core natural (BinaryPermutation.coreToNatural (Fin 12))
    (fun g v => BinaryPermutation.coreToNatural_equivariant g v)
    (BinaryPermutation.coreToNatural_surjective (Ω := Fin 12)) A ho
  have hker_le : (BinaryPermutation.coreToNatural (Fin 12)).ker ≤
      Representation.BinaryOffender.fixedSpace core A := by
    intro v hv
    apply (Representation.BinaryOffender.mem_fixedSpace_iff core A v).mpr
    intro a ha
    apply Subtype.ext
    have hv' : (BinaryPermutation.constants (Fin 12)).mkQ v.val = 0 :=
      congrArg Subtype.val hv
    obtain ⟨c, hc⟩ := (BinaryPermutation.mem_constants_iff v.val).mp
      ((Submodule.Quotient.mk_eq_zero (BinaryPermutation.constants (Fin 12))).mp hv')
    change BinaryPermutation.representation (Fin 12) a v.val = v.val
    ext i
    simp only [BinaryPermutation.representation_apply]
    rw [hc, hc]
  have hqrank := (BinaryPermutation.coreToNatural (Fin 12)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (BinaryPermutation.coreToNatural_surjective (Ω := Fin 12)),
    finrank_top, BinaryPermutation.finrank_natural_even (Fin 12) (by decide),
    BinaryPermutation.finrank_core] at hqrank
  rw [Fintype.card_fin] at hqrank
  have hkerfin : Module.finrank (ZMod 2)
      (BinaryPermutation.coreToNatural (Fin 12)).ker = 1 := by omega
  have hinf : (BinaryPermutation.coreToNatural (Fin 12)).ker ⊓
      Representation.BinaryOffender.fixedSpace core A =
        (BinaryPermutation.coreToNatural (Fin 12)).ker := by
    apply le_antisymm inf_le_left
    exact le_inf le_rfl hker_le
  rw [hinf, hkerfin] at hnat
  have hfd := Representation.BinaryOffender.fixedCodim_add_finrank natural A
  have hff := Representation.BinaryOffender.fixedCodim_add_finrank full A
  rw [BinaryPermutation.finrank_natural_even (Fin 12) (by decide),
    Fintype.card_fin] at hfd
  rw [BinaryPermutation.finrank_full] at hff
  rw [Fintype.card_fin] at hff
  change fixedCodim natural A = fixedCodim full A
  omega

/-- Every odd-prime element of `M₁₂` has displacement at least six on the
native ten-dimensional permutation heart. -/
public theorem six_le_fixedCodim_odd_prime (x : Sporadic.Mathieu.M12)
    (hp : (orderOf x).Prime) (ho : orderOf x ≠ 2) :
    6 ≤ fixedCodim m12HeartRepresentation (Subgroup.zpowers x) := by
  have hcomp :
      fixedCodim m12HeartRepresentation (Subgroup.zpowers x) =
        fixedCodim (BinaryPermutation.naturalRepresentation (Fin 12))
          ((Subgroup.zpowers x).map Sporadic.Mathieu.M12.subtype) := by
    change fixedCodim
      ((BinaryPermutation.naturalRepresentation (Fin 12)).comp
        Sporadic.Mathieu.M12.subtype) (Subgroup.zpowers x) = _
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  rw [hcomp, MonoidHom.map_zpowers]
  have horder : orderOf (x : Equiv.Perm (Fin 12)) = orderOf x :=
    Subgroup.orderOf_coe x
  have hoddA : Odd (Nat.card (Subgroup.zpowers (x : Equiv.Perm (Fin 12)))) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, horder]
    exact hp.odd_of_ne_two ho
  have hnative : 6 ≤ fixedCodim (BinaryPermutation.naturalRepresentation (Fin 12))
      (Subgroup.zpowers (x : Equiv.Perm (Fin 12))) := by
    rw [m12_natural_fixedCodim_eq_full_of_odd _ hoddA]
    rw [BinaryPermutation.fixedCodim_full_eq_card_sub_card_orbits]
    have hle := m12_prime_order_orbits_le_six x hp ho
    apply Nat.le_sub_of_add_le
    simpa only [Fintype.card_fin] using (show 6 +
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (x : Equiv.Perm (Fin 12)))
        (Fin 12)) ≤ 12 by omega)
  simpa only [Subgroup.subtype_apply] using hnative

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations

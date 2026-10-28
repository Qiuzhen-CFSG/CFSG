module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoComplement.Relations
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Coordinates on elementary preimages of the literal J4 core

The certified binary masks give an equivalence with the actual core, preserving
XOR and the two right-conjugation matrices. Exponent two makes its preimage a
binary vector space. A linear functional separating the nonidentity kernel
element, combined with the quotient coordinates, gives twelve coordinates.
The kernel has exactly two elements, so this map is both injective and
surjective. No invariance of the initial functional is assumed.

Source: ATLAS `J4G1-max1W1` through the certified core coordinates;
Aschbacher–Smith I.1.5, printed p.408, and GLS3 Section 6.1.
-/

@[expose] public section
namespace Janko4.TwoPrimary.InvariantComplement
open Cardinality Cardinality.KernelCount Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.KernelOrbits
open Max1RelativeRigidity.RelativeCocycles (actX_toNat actY_toNat)
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

/-- Evaluation in the literal, certified core. -/
def coreEval (v : V) : Core := maskValue matrixA_mul_self matrixB_pow_four v.toNat

theorem coreEval_zero : coreEval 0 = 1 := maskValue_zero matrixA_mul_self matrixB_pow_four

theorem coreEval_xor (v w : V) : coreEval (v ^^^ w) = coreEval v * coreEval w := by
  exact maskValue_xor matrixA_mul_self matrixB_pow_four v.toNat w.toNat

theorem coreEval_injective : Function.Injective coreEval := by
  intro v w h
  have he := coordinates_injective matrixA_mul_self matrixB_pow_four h
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  exact congrFun he ⟨i, hi⟩

theorem coreEval_surjective : Function.Surjective coreEval := by
  intro n
  obtain ⟨v, hv⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four n
  exact ⟨BitVec.ofNatLT v.val v.isLt, hv⟩

noncomputable def coreEquiv : V ≃ Core :=
  Equiv.ofBijective coreEval ⟨coreEval_injective, coreEval_surjective⟩

theorem coreEquiv_apply (v : V) : coreEquiv v = coreEval v := rfl

theorem coreEval_step (s : Bool) (v : V) :
    (coreEval (quotientStep s v) : Local) =
      (if s then y else x)⁻¹ * (coreEval v : Local) * (if s then y else x) := by
  cases s
  · change (maskValue matrixA_mul_self matrixB_pow_four
      (Max1RelativeRigidity.RelativeCocycles.actX v).toNat : Local) = _
    rw [actX_toNat]
    exact (right_conj_mask_x matrixA_mul_self matrixB_pow_four v.toNat).symm
  · change (maskValue matrixA_mul_self matrixB_pow_four
      (Max1RelativeRigidity.RelativeCocycles.actY v).toNat : Local) = _
    rw [actY_toNat]
    exact (right_conj_mask_y matrixA_mul_self matrixB_pow_four v.toNat).symm

/-- A field element is encoded by its single bit. -/
def bitHom : ZMod 2 →+ Bool where
  toFun t := decide (t = 1)
  map_zero' := rfl
  map_add' := by decide +kernel

theorem bitHom_one : bitHom 1 = true := rfl

open scoped IsMulCommutative

/-- Exponent two alone supplies a character nonzero on a specified nonidentity
central-kernel element. Invariance is imposed later by the matrix certificate. -/
theorem exists_separating_character {L : Type*} [Group L]
    (q : L →* Local) (he : ElementaryPreimage q) (z : q.ker) (hz : z ≠ 1) :
    ∃ f : Core.comap q →* Multiplicative Bool,
      f ⟨z.val, by change q z.val ∈ Core; rw [z.property]; exact Core.one_mem⟩ =
        Multiplicative.ofAdd true := by
  let N := Core.comap q
  let : IsMulCommutative N := ⟨⟨fun n m => Subtype.ext
    (elementary_preimage_commute q he n.property m.property).eq⟩⟩
  let : IsElementaryAbelian 2 N := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun n => Subtype.ext (he n.val n.property)) }
  let zN : N := ⟨z.val, by change q z.val ∈ Core; rw [z.property]; exact Core.one_mem⟩
  have hzne : (Additive.ofMul zN : Additive N) ≠ 0 := by
    intro h
    apply hz
    apply Subtype.ext
    exact congrArg (fun n : Additive N => n.toMul.val) h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hzne
  refine ⟨(bitHom.comp φ.toAddMonoidHom).toMultiplicativeRight, ?_⟩
  change Multiplicative.ofAdd (bitHom (φ (Additive.ofMul zN))) = _
  rw [hφ, bitHom_one]

/-- Arbitrary additive coordinates above the certified core, before imposing
conjugation invariance. -/
structure PreCoordinates {L : Type*} [Group L] (q : L →* Local) (z : q.ker) where
  equiv : Core.comap q ≃ V × Bool
  map_one : equiv 1 = (0, false)
  map_mul : ∀ n m, equiv (n * m) =
    ((equiv n).1 ^^^ (equiv m).1, (equiv n).2 + (equiv m).2)
  map_central : equiv ⟨z.val, by
    change q z.val ∈ Core; rw [z.property]; exact Core.one_mem⟩ = (0, true)
  map_projection : ∀ n, (coreEval (equiv n).1 : Local) = q n.val

/-- A separating character and the actual quotient coordinates give the
required twelve binary coordinates, with the central line last. -/
theorem exists_preCoordinates {L : Type*} [Group L]
    (q : L →* Local) (hq : Function.Surjective q) (hk : Nat.card q.ker = 2)
    (he : ElementaryPreimage q) (z : q.ker) (hz : z ≠ 1) :
    Nonempty (PreCoordinates q z) := by
  classical
  obtain ⟨f, hfz⟩ := exists_separating_character q he z hz
  let N := Core.comap q
  let zN : N := ⟨z.val, by change q z.val ∈ Core; rw [z.property]; exact Core.one_mem⟩
  let qN : N →* Core := (q.comp N.subtype).codRestrict _ (fun n => n.property)
  let e0 : N → V × Bool := fun n => (coreEquiv.symm (qN n), (f n).toAdd)
  have hp (n : N) : coreEval (e0 n).1 = qN n := coreEquiv.apply_symm_apply _
  have h0 : e0 1 = (0, false) := by
    apply Prod.ext
    · apply coreEval_injective
      rw [hp, _root_.map_one, coreEval_zero]
    · exact congrArg Multiplicative.toAdd f.map_one
  have hmul (n m : N) : e0 (n * m) =
      ((e0 n).1 ^^^ (e0 m).1, (e0 n).2 + (e0 m).2) := by
    apply Prod.ext
    · apply coreEval_injective
      rw [hp, _root_.map_mul, coreEval_xor, hp, hp]
    · exact congrArg Multiplicative.toAdd (f.map_mul n m)
  have hz0 : e0 zN = (0, true) := by
    apply Prod.ext
    · apply coreEval_injective
      rw [hp, coreEval_zero]
      exact Subtype.ext z.property
    · exact congrArg Multiplicative.toAdd hfz
  obtain ⟨z₀, hz₀, huniq⟩ := (Nat.card_eq_two_iff' (1 : q.ker)).mp hk
  have uniq (w : q.ker) (hw : w ≠ 1) : w = z :=
    (huniq w hw).trans (huniq z hz).symm
  have hinj : Function.Injective e0 := by
    intro n m h
    have hqnm : q n.val = q m.val := congrArg Subtype.val
      (coreEquiv.symm.injective (congrArg Prod.fst h))
    have hfnm : f n = f m := Multiplicative.toAdd.injective (congrArg Prod.snd h)
    let u : N := n * m⁻¹
    have huq : q u.val = 1 := by
      change q (n.val * m.val⁻¹) = 1
      rw [_root_.map_mul, _root_.map_inv, hqnm, mul_inv_cancel]
    by_cases hu : u = 1
    · exact mul_inv_eq_one.mp hu
    have huz : u = zN := Subtype.ext (congrArg (fun w : q.ker => (w : L))
      (uniq ⟨u.val, huq⟩ (fun hh => hu (Subtype.ext (congrArg (fun w : q.ker => (w : L)) hh)))))
    have hfu : f u = 1 := by
      change f (n * m⁻¹) = 1
      rw [_root_.map_mul, _root_.map_inv, hfnm, mul_inv_cancel]
    rw [huz, hfz] at hfu
    exact Bool.noConfusion (congrArg Multiplicative.toAdd hfu)
  have hsurj : Function.Surjective e0 := by
    rintro ⟨v, t⟩
    obtain ⟨l, hl⟩ := hq (coreEval v).val
    let n : N := ⟨l, by change q l ∈ Core; rw [hl]; exact (coreEval v).property⟩
    have hnv : (e0 n).1 = v := by
      apply coreEval_injective
      rw [hp]
      exact Subtype.ext hl
    by_cases hn : (f n).toAdd = t
    · exact ⟨n, Prod.ext hnv hn⟩
    · refine ⟨n * zN, ?_⟩
      rw [hmul, hz0, hnv]
      change (v ^^^ 0#11, (f n).toAdd + true) = (v, t)
      rw [BitVec.xor_zero]
      apply Prod.ext
      · rfl
      · exact (by decide +kernel : ∀ a b : Bool, a ≠ b → a + true = b)
          (f n).toAdd t hn
  let e := Equiv.ofBijective e0 ⟨hinj, hsurj⟩
  exact ⟨{
    equiv := e
    map_one := h0
    map_mul := hmul
    map_central := hz0
    map_projection := fun n => congrArg Subtype.val (hp n) }⟩

end Janko4.TwoPrimary.InvariantComplement

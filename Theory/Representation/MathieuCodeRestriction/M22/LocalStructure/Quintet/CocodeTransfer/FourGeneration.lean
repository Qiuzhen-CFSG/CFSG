module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.FixedGeneration
public import Theory.Representation.SubspaceQuotient
public import Theory.ElementaryAbelian.FixedOrderGeneration
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Generation by fixed spaces of elementary four-subgroups

An elementary group of order at least eight moving a vector along a fixed
binary line has an elementary four-subgroup fixing that vector. Indeed, the
displacement homomorphism has image of order at most two, so its kernel has
order at least four. This generates any space with such a displacement law.

Conjugation permutes the four-subgroups and their fixed spaces. Consequently,
if the generated space contains an invariant middle term and a fixed vector
outside it, irreducibility of the top section forces generation of the whole
module. This is the linear generation argument used in Aschbacher--Smith,
H.15.4(4), printed p.400 (combined manuscript of 1 March 2004).
-/

public section

noncomputable section
open Representation.BinaryOffender
namespace MathieuCode.M22Quintet.CocodeTransfer
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Conjugation permutes the elementary four-subgroups and their fixed spaces. -/
theorem fourFixedSpan_invariant (ρ : Representation (ZMod 2) G V)
    (K H : Subgroup G) (hN : H ≤ Subgroup.normalizer (K : Set G))
    (g : H) (v : V) (hv : v ∈ fourFixedSpan ρ K) :
    ρ g.val v ∈ fourFixedSpan ρ K := by
  have hle : fourFixedSpan ρ K ≤ (fourFixedSpan ρ K).comap (ρ g.val) := by
    refine iSup_le fun B => iSup_le fun hBK => iSup_le fun hB => iSup_le fun hc => ?_
    let := hB
    let B' := B.map (MulAut.conj g.val).toMonoidHom
    have hB' : B' ≤ K := by
      rintro _ ⟨b, hb, rfl⟩
      exact (hN g.property b).mp (hBK hb)
    have hcard : Nat.card B' = 4 :=
      (Subgroup.card_map_of_injective (MulAut.conj g.val).injective).trans hc
    have hspan : fixedSpace ρ B' ≤ fourFixedSpan ρ K :=
      le_iSup_of_le B' (le_iSup_of_le hB'
        (le_iSup_of_le (IsElementaryAbelian.map (MulAut.conj g.val).toMonoidHom)
          (le_iSup_of_le hcard le_rfl)))
    intro w hw
    apply hspan
    intro b
    obtain ⟨a, ha, he⟩ := b.property
    have haFix : ρ a w = w := hw ⟨a,ha⟩
    have hi : ρ g.val⁻¹ (ρ g.val w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    change ρ b.val (ρ g.val w) = ρ g.val w
    rw [← he]
    change ρ (g.val * a * g.val⁻¹) (ρ g.val w) = ρ g.val w
    rw [map_mul, map_mul]
    change ρ g.val (ρ a (ρ g.val⁻¹ (ρ g.val w))) = ρ g.val w
    rw [hi, haFix]
  exact hle hv

/-- A vector moved only along a fixed line by an elementary group of order at
least eight is fixed by an elementary four-subgroup of that group. -/
theorem mem_fourFixedSpan_of_line_displacement [Finite G]
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [IsElementaryAbelian 2 K]
    (hK : 8 ≤ Nat.card K) (C : Submodule (ZMod 2) V)
    [FiniteDimensional (ZMod 2) C] (hC : Module.finrank (ZMod 2) C = 1)
    (hfix : C ≤ fixedSpace ρ K) (v : V)
    (hmove : ∀ k : K, ρ k.val v - v ∈ C) : v ∈ fourFixedSpan ρ K := by
  let d : K →* Multiplicative C := {
    toFun k := Multiplicative.ofAdd ⟨ρ k.val v - v, hmove k⟩
    map_one' := by
      apply Subtype.ext
      change ρ (1 : G) v - v = 0
      simp
    map_mul' k l := by
      apply Subtype.ext
      change ρ (k.val * l.val) v - v = (ρ k.val v - v) + (ρ l.val v - v)
      have he := hfix (hmove l) k
      change ρ k.val (ρ l.val v - v) = ρ l.val v - v at he
      rw [map_sub] at he
      rw [map_mul, Module.End.mul_apply]
      calc
        _ = (ρ k.val (ρ l.val v) - ρ k.val v) + (ρ k.val v - v) := by abel
        _ = _ := by rw [he]; abel }
  have hcardC : Nat.card (Multiplicative C) = 2 := by
    change Nat.card C = 2
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hC, Nat.card_zmod, pow_one]
  let : Finite (Multiplicative C) := Nat.finite_of_card_ne_zero (by omega)
  have hrange : Nat.card d.range ≤ 2 := by
    calc
      Nat.card d.range ≤ Nat.card (Multiplicative C) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = 2 := hcardC
  have hmul := d.ker.card_mul_index
  rw [Subgroup.index_ker] at hmul
  have hker : 4 ≤ Nat.card d.ker := by nlinarith
  let : IsElementaryAbelian 2 d.ker := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun k => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 K) k.val }
  obtain ⟨B, hB, hBe, hc, _⟩ := IsElementaryAbelian.exists_two_power_subgroup_mem
    d.ker (n := 2) (by decide) hker 1 d.ker.one_mem
  let := hBe
  have hc' : Nat.card (B.map K.subtype) = 4 :=
    (Subgroup.card_map_of_injective K.subtype_injective).trans hc
  have hvB : v ∈ fixedSpace ρ (B.map K.subtype) := by
    intro b
    obtain ⟨a, ha, he⟩ := b.property
    have hz : d a = 1 := hB ha
    have hz' : ρ a.val v - v = 0 := congrArg (fun x : Multiplicative C => x.toAdd.val) hz
    change ρ b.val v = v
    rw [← he]
    exact sub_eq_zero.mp hz'
  have hspan : fixedSpace ρ (B.map K.subtype) ≤ fourFixedSpan ρ K :=
    le_iSup_of_le (B.map K.subtype) (le_iSup_of_le (Subgroup.map_subtype_le B)
      (le_iSup_of_le (IsElementaryAbelian.map K.subtype) (le_iSup_of_le hc' le_rfl)))
  exact hspan hvB

/-- Once the middle space is generated, an invariant four-fixed span containing
one vector above an irreducible quotient is the entire module. -/
theorem fourFixedSpan_eq_top_of_middle_and_escape
    (ρ : Representation (ZMod 2) G V) (K H : Subgroup G) (hN : H ≤ Subgroup.normalizer (K : Set G))
    (W : Subrepresentation (ρ.comp H.subtype))
    [Representation.IsIrreducible W.quotientRepresentation]
    (hW : W.toSubmodule ≤ fourFixedSpan ρ K)
    (B : Subgroup G) (hBK : B ≤ K) (hBe : IsElementaryAbelian 2 B)
    (hc : Nat.card B = 4) (hescape : ¬ fixedSpace ρ B ≤ W.toSubmodule) :
    fourFixedSpan ρ K = ⊤ := by
  let F : Subrepresentation (ρ.comp H.subtype) := {
    toSubmodule := fourFixedSpan ρ K
    apply_mem_toSubmodule := fourFixedSpan_invariant ρ K H hN }
  rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient W F with h | h
  · exfalso
    apply hescape
    have hspan : fixedSpace ρ B ≤ fourFixedSpan ρ K :=
      le_iSup_of_le B (le_iSup_of_le hBK
        (le_iSup_of_le hBe (le_iSup_of_le hc le_rfl)))
    exact hspan.trans h
  · change W.toSubmodule ⊔ fourFixedSpan ρ K = ⊤ at h
    simpa only [sup_eq_right.mpr hW] using h

end MathieuCode.M22Quintet.CocodeTransfer

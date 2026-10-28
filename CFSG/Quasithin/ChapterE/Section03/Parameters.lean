module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Rigidity
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF

/-!
# Weak-closure parameters and their first applications

This module assembles Aschbacher–Smith E.3.1–11: the genuine module and global
parameters, centralizer rigidity, fixed-space families, and the non-FF obstruction.

For E.3.7, conjugation invariance transports the bound on `s` to E.3.6.
For E.3.10, each subgroup of the induced automizer lifts to a subgroup of the
actor with the same relative index. Additivity of binary coranks then permits
E.3.7 to identify its fixed space. The nontrivial commutator rules out a trivial
image, and membership in the fixed-space family bounds `a`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.3.1–11,
printed pp. 231–232 (PDF pp. 242–243).
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- Aschbacher–Smith E.3.7: a subgroup of the conjugate normalizer of corank
below `s` has the same centralizer in `V` as the whole conjugate. -/
theorem lemma_E_3_7 {V B : Subgroup G} [IsElementaryAbelian 2 V] (g : G)
    (hB : B ≤ V.map (MulAut.conj g).toMonoidHom ⊓ normalizer (V : Set G))
    (hb : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B : ℕ∞) < globalS V) :
    V ⊓ centralizer (B : Set G) =
      V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  apply centralizer_inf_eq_of_corank_lt_globalS (hB.trans inf_le_left)
  · rwa [globalS_map_equiv]
  · exact IsElementaryAbelian.isPGroup 2 V

private theorem corank_add {W A B : Subgroup G} [IsElementaryAbelian 2 W]
    (hBA : B ≤ A) (hAW : A ≤ W) :
    subgroupCorank W B = subgroupCorank A B + subgroupCorank W A := by
  let _ : IsElementaryAbelian 2 A := {
    toIsMulCommutative := isMulCommutative_iff.mpr (fun a b =>
      (Subgroup.inclusion_injective hAW) (by
        simpa only [map_mul] using mul_comm (Subgroup.inclusion hAW a) (Subgroup.inclusion hAW b)))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : G) (hAW a.property))) }
  have h := Subgroup.relIndex_mul_relIndex B A W hBA hAW
  have hp (T U : Subgroup G) [IsElementaryAbelian 2 T] :
      U.relIndex T = 2 ^ subgroupCorank T U := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact Subgroup.relIndex_eq_two_pow_quotient_finrank T U
  rw [hp A B, hp W A, hp W B, ← pow_add] at h
  exact ((Nat.pow_right_injective (by decide : 2 ≤ 2)) h).symm

omit [Finite G] in
private theorem lift_image_subgroup {V A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G))
    (D : Subgroup (Automizer V)) (hD : D ≤ inducedAutomizer V A) :
    ∃ B ≤ A, inducedAutomizer V B = D ∧
      subgroupCorank A B = Nat.log 2 (D.relIndex (inducedAutomizer V A)) := by
  let N := normalizer (V : Set G)
  let f := V.normalizerMonoidHom.rangeRestrict
  let C := A.subgroupOf N
  let L := C ⊓ D.comap f
  let B := L.map N.subtype
  have hBA : B ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have hBN : B.subgroupOf N = L := by
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective L
  have hmap : L.map f = D := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro d hd
      obtain ⟨x, hx, he⟩ := hD hd
      exact ⟨x, ⟨hx, (show f x ∈ D from he.symm ▸ hd)⟩, he⟩
  refine ⟨B, hBA, ?_, ?_⟩
  · change (B.subgroupOf N).map f = D
    rw [hBN, hmap]
  · unfold subgroupCorank
    congr 1
    rw [← Subgroup.relIndex_subgroupOf (H := B) hA, hBN]
    exact (Subgroup.inf_relIndex_left C (D.comap f)).trans
      (Subgroup.relIndex_comap D f C)

omit [Finite G] in
private theorem fixedSpace_eq_of_centralizer_eq {V A B : Subgroup G}
    [IsElementaryAbelian 2 V]
    (hA : A ≤ normalizer (V : Set G)) (hB : B ≤ normalizer (V : Set G))
    (h : V ⊓ centralizer (A : Set G) = V ⊓ centralizer (B : Set G)) :
    fixedSpace (automizerRepresentation V) (inducedAutomizer V A) =
      fixedSpace (automizerRepresentation V) (inducedAutomizer V B) := by
  ext v
  rw [mem_fixedSpace_inducedAutomizer V A hA, mem_fixedSpace_inducedAutomizer V B hB]
  have hv := congrArg (fun S : Subgroup G => (v.toMul : G) ∈ S) h
  simpa only [Subgroup.mem_inf, v.toMul.property, true_and] using (iff_of_eq hv)

/-- The fixed-space family conclusion of E.3.10 holds for any subgroup of
`N_{Vᵍ}(V)` of sufficiently small corank in `Vᵍ`. Nontriviality of the induced
automizer is deduced from the nontrivial commutator. -/
theorem inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS {V A : Subgroup G} [IsElementaryAbelian 2 V] (g : G)
    (hA : A ≤ V.map (MulAut.conj g).toMonoidHom ⊓ normalizer (V : Set G))
    (hb : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A : ℕ∞) < globalS V)
    (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    V ⊓ centralizer (A : Set G) =
        V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
      inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V)
        ((globalS V).toNat - subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A) := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hAW : A ≤ W := hA.trans inf_le_left
  have hAN := hA.trans inf_le_right
  let _ : IsElementaryAbelian 2 A := {
    toIsMulCommutative := isMulCommutative_iff.mpr (fun a b =>
      (Subgroup.inclusion_injective hAW) (by
        simpa only [map_mul] using mul_comm (Subgroup.inclusion hAW a) (Subgroup.inclusion hAW b)))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : G) (hAW a.property))) }
  have hs : ((globalS V).toNat : ℕ∞) = globalS V :=
    ENat.natCast_toNat (globalS_ne_top V)
  have hb' : subgroupCorank W A < (globalS V).toNat := by
    apply ENat.natCast_lt_natCast.mp
    rwa [hs]
  have heq := lemma_E_3_7 g hA hb
  refine ⟨heq, Nat.sub_pos_of_lt hb', ⟨?_, inducedAutomizer_elementary V A hAN⟩, ?_⟩
  · intro hbot
    have hc : V ≤ centralizer (A : Set G) :=
      le_centralizer_iff.mpr ((inducedAutomizer_eq_bot_iff hAN).mp hbot)
    have hcW : V ≤ centralizer (W : Set G) := by
      have heq' : V ⊓ centralizer (W : Set G) = V :=
        heq.symm.trans (inf_eq_left.mpr hc)
      exact inf_eq_left.mp heq'
    exact hcomm (commutator_eq_bot_iff_le_centralizer.mpr hcW)
  · intro D hDA hD
    obtain ⟨B, hBA, hBI, hcorank⟩ := lift_image_subgroup hAN D hDA
    have hD' : subgroupCorank A B < (globalS V).toNat - subgroupCorank W A := by
      rw [hcorank]
      exact hD
    have hBN := hBA.trans hAN
    have hB : (subgroupCorank W B : ℕ∞) < globalS V := by
      rw [← hs]
      apply ENat.natCast_lt_natCast.mpr
      rw [corank_add hBA hAW]
      omega
    have hcent := lemma_E_3_7 g (hBA.trans hA) hB
    rw [← hBI]
    exact fixedSpace_eq_of_centralizer_eq hAN hBN (heq.trans hcent.symm)

/-- Aschbacher–Smith E.3.10, including centralizer equality, membership of the
actual induced automizer in `A_{s-b}`, and both numerical inequalities.
The natural value of `s` is legitimate because `globalS_ne_top` proves finiteness. -/
theorem lemma_E_3_10 (V : Subgroup G) [IsElementaryAbelian 2 V] (g : G)
    (hb : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ normalizer (V : Set G)) : ℕ∞) < globalS V)
    (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    let W := V.map (MulAut.conj g).toMonoidHom
    let A := W ⊓ normalizer (V : Set G)
    let b := subgroupCorank W A
    V ⊓ centralizer (A : Set G) = V ⊓ centralizer (W : Set G) ∧
      inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V)
        ((globalS V).toNat - b) ∧
      globalS V - localA V ≤ (b : ℕ∞) ∧ (b : ℕ∞) < globalS V := by
  dsimp only
  obtain ⟨heq, hfamily⟩ := inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS g le_rfl hb hcomm
  refine ⟨heq, hfamily, ?_, hb⟩
  have ha := le_moduleA_of_mem (automizerRepresentation V) hfamily
  have hs : ((globalS V).toNat : ℕ∞) = globalS V :=
    ENat.natCast_toNat (globalS_ne_top V)
  rw [ENat.natCast_sub, hs] at ha
  exact tsub_le_iff_tsub_le.mp ha
end CFSG.Quasithin.ChapterE

module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Normalizing cyclic TI conjugates commute

The action of one cyclic subgroup on the other has a nontrivial kernel,
since the automorphism group has Euler-totient order. The TI condition then
forces normalization in the reverse direction, and disjointness kills the
commutators. Actor TI is transported by the actual conjugation maps.

This is the finite cyclic argument used to exclude the singleton and
swapped local alternatives in the maximal-intersection approach to
Aschbacher–Smith E.6.24, printed p.255.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace Representation.RegularCyclicNormalClosure.FactorConstruction
variable {A : Type*} [Group A]

private theorem map_conj_comp (C : Subgroup A) (a b : A) :
    (C.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      C.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext c
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

/-- Actor TI is preserved by actual conjugation. -/
theorem disjoint_conjugates_of_conjugate
    (C : Subgroup A)
    (hTI : ∀ b : A, C.map (MulAut.conj b).toMonoidHom ≠ C →
      Disjoint C (C.map (MulAut.conj b).toMonoidHom)) (a b : A)
    (hne : (C.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom ≠
      C.map (MulAut.conj a).toMonoidHom) :
    Disjoint (C.map (MulAut.conj a).toMonoidHom)
      ((C.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom) := by
  have hn : C.map (MulAut.conj (a⁻¹ * b * a)).toMonoidHom ≠ C := by
    intro he
    apply hne
    have hh := congrArg (fun D : Subgroup A => D.map (MulAut.conj a).toMonoidHom) he
    rw [map_conj_comp] at hh ⊢
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh
  have hd := Subgroup.disjoint_map (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective (hTI _ hn)
  rw [map_conj_comp] at hd ⊢
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hd

/-- A cyclic TI pair of equal nontrivial finite order that normalizes in
one direction commutes. The automorphism action has a nontrivial kernel
because Euler's totient is smaller than the common subgroup order. -/
theorem commute_of_cyclic_ti_of_normalizes [Finite A]
    (C D : Subgroup A) (hcyc : IsCyclic C) (hcard : Nat.card D = Nat.card C)
    (hcard1 : 1 < Nat.card C) (hdis : Disjoint C D)
    (hTI : ∀ a : A, D.map (MulAut.conj a).toMonoidHom ≠ D →
      Disjoint D (D.map (MulAut.conj a).toMonoidHom))
    (hn : D ≤ normalizer (C : Set A)) :
    ∀ c ∈ C, ∀ d ∈ D, Commute c d := by
  let := hcyc
  let f : D →* MulAut C := C.normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hnot : ¬ Function.Injective f := by
    intro hi
    have hh := Nat.card_le_card_of_injective f hi
    rw [IsCyclic.card_mulAut, hcard] at hh
    exact (Nat.not_le_of_lt (Nat.totient_lt _ hcard1)) hh
  obtain ⟨z, hz, hzne⟩ : ∃ z : D, f z = 1 ∧ z ≠ 1 := by
    by_contra he
    apply hnot
    apply (injective_iff_map_eq_one f).mpr
    intro z hz
    by_contra hzne
    exact he ⟨z, hz, hzne⟩
  have hzcent : (z : A) ∈ centralizer (C : Set A) := by
    have hh : Subgroup.inclusion hn z ∈ C.normalizerMonoidHom.ker := hz
    rwa [Subgroup.normalizerMonoidHom_ker] at hh
  have hCn : C ≤ normalizer (D : Set A) := by
    intro c hc
    apply mem_normalizer_iff_map_conj_eq.mpr
    by_contra hne
    have hzmap : (z : A) ∈ D.map (MulAut.conj c).toMonoidHom := by
      refine ⟨z, z.property, ?_⟩
      change c * (z : A) * c⁻¹ = z
      rw [(mem_centralizer_iff.mp hzcent c hc), mul_inv_cancel_right]
    exact hzne (Subtype.ext (Subgroup.disjoint_def.mp (hTI c hne) z.property hzmap))
  intro c hc d hd
  have heC : c * d * c⁻¹ * d⁻¹ ∈ C := by
    have hh := C.mul_mem hc ((mem_normalizer_iff.mp (hn hd) c⁻¹).mp (C.inv_mem hc))
    simpa only [mul_assoc] using hh
  have heD : c * d * c⁻¹ * d⁻¹ ∈ D :=
    D.mul_mem ((mem_normalizer_iff.mp (hCn hc) d).mp hd) (D.inv_mem hd)
  have he := Subgroup.disjoint_def.mp hdis heC heD
  change c * d = d * c
  have hh := congrArg (fun x : A => x * (d * c)) he
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, mul_one, one_mul] using hh

end Representation.RegularCyclicNormalClosure.FactorConstruction

namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- An actor conjugate normalizing the original cyclic actor commutes with it. -/
theorem Input.commute_of_conjugate_le_normalizer (h : Input ρ C) (a : A)
    (hn : C.map (MulAut.conj a).toMonoidHom ≤ normalizer (C : Set A)) :
    ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d := by
  by_cases he : C.map (MulAut.conj a).toMonoidHom = C
  · rw [he]
    let := h.cyclic
    intro c hc d hd
    exact (Commute.all (⟨c, hc⟩ : C) ⟨d, hd⟩).map C.subtype
  · apply commute_of_cyclic_ti_of_normalizes C _ h.cyclic
      (Subgroup.card_map_of_injective (MulAut.conj a).injective)
      (C.one_lt_card_iff_ne_bot.mpr h.nontrivial) (h.disjoint_conjugate_of_ne a he) _ hn
    exact disjoint_conjugates_of_conjugate C h.disjoint_conjugate_of_ne a

end Representation.RegularCyclicNormalClosure

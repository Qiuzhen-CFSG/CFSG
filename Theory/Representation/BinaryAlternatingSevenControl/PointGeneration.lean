module
public import Theory.Representation.BinaryAlternatingSevenControl.FixedLine
public import Theory.Representation.BinaryConjugationSection

/-!
# Point centralizers generate the faithful binary A₇ four-space action

Every nonzero vector spans the fixed space of some Sylow two-subgroup.
Its pointwise stabilizer is therefore maximal. Two distinct nonzero vectors
cannot have nested stabilizers: a Sylow subgroup fixing the second would
then fix the first, contradicting its unique fixed line. Their stabilizers
generate A₇. Pullback through a surjective actor and the literal conjugation
coordinates gives generation by the original point centralizers upstairs.

Source: Aschbacher--Smith, the final A₇ argument in 12.2.19, printed p.802,
using the four-space geometry of C.1.23(2), p.130.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped Pointwise
namespace Representation.BinaryAlternatingSevenControl
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem exists_sylow_fixed_span (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {v : V} (hv : v ≠ 0) :
    ∃ S : Sylow 2 A7, fixedSpace ρ S = Submodule.span (ZMod 2) {v} := by
  let R : Sylow 2 A7 := Classical.choice inferInstance
  obtain ⟨u,hu,hfix,_⟩ := sylow_fixed_line ρ hf hd R
  obtain ⟨g,hg⟩ := transitive ρ hf hd hu hv
  let S : Sylow 2 A7 := g • R
  have hvS : v ∈ fixedSpace ρ S := by
    rintro ⟨a,ha⟩
    obtain ⟨b,hb,rfl⟩ := ha
    rw [← hg]
    change ρ (g*b*g⁻¹) (ρ g u) = ρ g u
    simp only [map_mul, Module.End.mul_apply, ρ.inv_self_apply]
    exact congrArg (ρ g) (hfix ⟨b,hb⟩)
  refine ⟨S, (Submodule.eq_of_le_of_finrank_eq
    (Submodule.span_le.mpr (by simpa using hvS)) ?_).symm⟩
  rw [finrank_span_singleton hv, sylow_fixed_finrank ρ hf hd S]

theorem distinct_vector_kernels_generate (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) :
    subspaceKernel ρ (Submodule.span (ZMod 2) {v}) ⊤ ⊔
      subspaceKernel ρ (Submodule.span (ZMod 2) {w}) ⊤ = ⊤ := by
  let Kv := subspaceKernel ρ (Submodule.span (ZMod 2) {v}) ⊤
  let Kw := subspaceKernel ρ (Submodule.span (ZMod 2) {w}) ⊤
  obtain ⟨R,hR⟩ := exists_sylow_fixed_span ρ hf hd hv
  have hc : IsCoatom Kv := by
    dsimp [Kv]
    rw [← hR]
    exact sylow_fixedKernel_coatom ρ hf hd R
  by_contra hn
  have he : Kv = Kv ⊔ Kw := by
    by_contra he
    exact hn (hc.2 _ (lt_of_le_of_ne le_sup_left he))
  have hle : Kw ≤ Kv := by rw [he]; exact le_sup_right
  obtain ⟨S,hS⟩ := exists_sylow_fixed_span ρ hf hd hw
  have hvS : v ∈ fixedSpace ρ S := by
    intro a
    have ha : (a : A7) ∈ Kw := ⟨mem_top _, fun y hy => (hS.symm ▸ hy) a⟩
    exact (hle ha).2 v (Submodule.subset_span (Set.mem_singleton v))
  rw [hS] at hvS
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hvS
  fin_cases c
  · change (0 : ZMod 2) • w = v at hc
    rw [zero_smul] at hc
    exact hv hc.symm
  · change (1 : ZMod 2) • w = v at hc
    rw [one_smul] at hc
    exact hvw hc.symm

end Representation.BinaryAlternatingSevenControl

module

public import Theory.Representation.BinaryOffender.CentralizerField
public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Two-subgroups on Irr⁺ orbit modules

A two-subgroup centralizing the actor of an Irr⁺ member and stabilizing
that member acts trivially on it: its action lies in the odd-order linear
centralizer furnished by A.1.41. A normal subgroup centralizing a seed
centralizes its full orbit span. Faithfulness then kills that subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.1.41 and the proof of D.3.4(1), printed pp.31 and 194.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Representation.CentralizerField Representation.BinaryOffender.CentralizerField
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A two-group stabilizing an Irr⁺ member and centralizing its actor
acts trivially on that member. -/
theorem IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes
    [FiniteDimensional (ZMod 2) V]
    {X P : Subgroup G} {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I)
    (hP : IsPGroup 2 P) (hPX : P ≤ centralizer (X : Set G))
    (hPI : P ≤ subspaceStabilizer ρ I) : I ≤ fixedSpace ρ P := by
  let σ := (invariantSubspace ρ X I hI.choose).toRepresentation
  let C := linearCentralizer σ
  let a := (stabilizerRepresentation ρ I).asGroupHom.comp (inclusion hPI)
  have ha (p : P) : a p ∈ C := by
    apply (mem_linearCentralizer_iff σ _).mpr
    intro x v
    apply Subtype.ext
    change ρ p (ρ x v) = ρ x (ρ p v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    rw [mem_centralizer_iff.mp (hPX p.property) x x.property]
  let f : P →* C := a.codRestrict C ha
  have hodd : Odd (Nat.card C) :=
    (centralizer_cyclic_odd ρ X I hI.choose hI.choose_spec.1 hI.choose_spec.2).2
  have hf (p : P) : f p = 1 := by
    obtain ⟨n, hn⟩ := hP p
    have hp : f p ^ 2 ^ n = 1 := by rw [← map_pow, hn, map_one]
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes
      (hodd.coprime_two_right.pow_right n)
      (orderOf_dvd_natCard (f p)) (orderOf_dvd_of_pow_eq_one hp)
  intro v hv p
  have hh := congrArg (fun c : C => c.val.val (⟨v, hv⟩ : I)) (hf p)
  exact congrArg Subtype.val hh

/-- A normal subgroup fixing a seed pointwise fixes its full orbit span. -/
theorem orbitSpan_le_fixedSpace_of_normal {P A : Subgroup G} [P.Normal]
    {I : Submodule (ZMod 2) V} (hI : I ≤ fixedSpace ρ P) :
    orbitSpan ρ A I ≤ fixedSpace ρ P := by
  apply iSup_le
  rintro a _ ⟨v, hv, rfl⟩ p
  have hc : (a : G)⁻¹ * p * a ∈ P := by
    simpa only [inv_inv] using
      (inferInstance : P.Normal).conj_mem p p.property (a : G)⁻¹
  have hh := hI hv ⟨(a : G)⁻¹ * p * a, hc⟩
  calc
    ρ p (ρ a v) = ρ a (ρ ((a : G)⁻¹ * p * a) v) := by
      simp only [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = ρ a v := congrArg (ρ a) hh

/-- Faithful generation by conjugates kills a normal subgroup fixing the seed. -/
theorem eq_bot_of_faithful_orbitSpan {P A : Subgroup G} [P.Normal]
    {I : Submodule (ZMod 2) V} (hf : Function.Injective ρ)
    (hI : I ≤ fixedSpace ρ P) (hgen : orbitSpan ρ A I = ⊤) : P = ⊥ := by
  apply bot_unique
  intro p hp
  apply mem_bot.mpr
  apply hf
  apply LinearMap.ext
  intro v
  have hh := orbitSpan_le_fixedSpace_of_normal ρ (A := A) hI
  rw [hgen] at hh
  simpa only [map_one, Module.End.one_apply, MonoidHom.comp_apply, Subgroup.subtype_apply]
    using hh Submodule.mem_top ⟨p, hp⟩

end Representation.BinaryOffender.Homogeneous

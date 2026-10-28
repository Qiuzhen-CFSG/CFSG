module

public import Theory.Mathieu.M24.Properties.Simplicity
public import Theory.GroupTheory.PCoreSurjective

/-!
# Two-group extensions of Mathieu layers

A group with a normal series consisting of a two-group, a direct power of
the concrete Mathieu group M24, and a two-group retains all extension kernels.
This is the shape needed when adjoining a two-group to a family of conjugate
local subgroups of shape E2048.M24. No splitting or module identification is
part of the definition.

Simplicity and the checked order of M24 show that its two-core is trivial.
Consequently every surjection to M24 with two-group kernel identifies that
kernel with the source's two-core.

Source for the local shape: GLS, *The Classification of the Finite Simple
Groups*, volume 3, Table 5.3i. The results here are general extension facts;
they do not assert a local subgroup classification for J4.
-/

@[expose] public section

namespace Sporadic.Mathieu

open Subgroup

/-- A normal series with two-group bottom and top factors and an actual
direct power of the Witt-design automorphism group in the middle. -/
def HasMathieuTwoLayer (K : Type*) [Group K] : Prop :=
  ∃ (N : Subgroup K) (_ : N.Normal), IsPGroup 2 N ∧
    ∃ (D : Subgroup (K ⧸ N)) (_ : D.Normal) (n : ℕ),
      Nonempty (D ≃* (Fin n → M24)) ∧ IsPGroup 2 ((K ⧸ N) ⧸ D)

/-- The simple Mathieu group of order divisible by three has trivial two-core. -/
theorem m24_twoCore : pCore 2 M24 = ⊥ := by
  let := m24_isSimpleGroup
  rcases (inferInstance : (pCore 2 M24).Normal).eq_bot_or_eq_top with h | h
  · exact h
  have hp : IsPGroup 2 M24 :=
    (pCore_isPGroup (p := 2) (G := M24)).of_equiv
      ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [m24_order] at hn
  have hd : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
  have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) hd
  norm_num at this

/-- A two-group kernel over M24 is the full two-core, including in
nonsplit extensions. -/
theorem ker_eq_twoCore_of_surjective_m24 {K : Type*} [Group K] [Finite K]
    (f : K →* M24) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker) :
    f.ker = pCore 2 K := by
  have he := f.comap_pCore_of_ker_isPGroup hf hp
  rw [m24_twoCore] at he
  exact he

end Sporadic.Mathieu

end

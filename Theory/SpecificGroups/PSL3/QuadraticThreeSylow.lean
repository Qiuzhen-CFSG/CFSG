module

public import Theory.SpecificGroups.GL2.FiniteQuadraticTorus
public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Theory.SpecificGroups.PSL3.ProjectionKernel
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# Cyclic Sylow three-subgroups of PSL₃ over fields of order −1 modulo three

The units of a quadratic extension embed in GL₂ by the regular representation,
and then in SL₃ by the determinant-corrected block embedding. When |F| ≡ −1
modulo three, the scalar kernel of SL₃ → PSL₃ is trivial. Thus the resulting
cyclic subgroup has order |F|² − 1 and index |F|³(|F|³ − 1), prime to three.
A Sylow three-subgroup of this torus is Sylow in the whole projective group;
Sylow conjugacy proves cyclicity for every Sylow three-subgroup.

This is the linear cyclic-Sylow calculation used in Aschbacher–Smith,
combined 1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.511
(PDF p.528). It applies to the actual projective matrix quotient and does
not make any assertion about universal central covers.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups

private theorem cyclic_sylow_of_cyclic_index {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) [IsCyclic C] (hi : ¬ 3 ∣ C.index) (P : Sylow 3 G) :
    IsCyclic P := by
  let T : Sylow 3 C := default
  let A := (T : Subgroup C).map C.subtype
  have ha : IsPGroup 3 A := T.isPGroup'.map C.subtype
  have hai : ¬ 3 ∣ A.index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.prime_three.not_dvd_mul T.not_dvd_index hi
  let U : Sylow 3 G := ha.toSylow hai
  let e := (T : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective
  have hc : IsCyclic U := e.isCyclic.mp inferInstance
  exact (U.equiv P).isCyclic.mp hc

namespace Matrix.PSL3.QuadraticThreeSylow
variable (F : Type*) [Field F] [Finite F]

theorem exists_cyclic_subgroup (p : ℕ) [Fact p.Prime] [CharP F p]
    (hF : Nat.card F % 3 = 2) :
    ∃ C : Subgroup PSL(3,F), IsCyclic C ∧
      Nat.card C = Nat.card F ^ 2 - 1 ∧ C.index = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) := by
  have hg : Nat.gcd 3 (Nat.card F - 1) = 1 := by
    apply Nat.Coprime.gcd_eq_one
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    omega
  have hp : Function.Injective (projection F) := by
    apply (projection F).ker_eq_bot_iff.mp
    apply (Subgroup.eq_bot_iff_card _).mpr
    rw [card_projectionKernel, hg]
  let E := FiniteField.Extension F p 2
  obtain ⟨ρ, _, hρ, _⟩ := Matrix.GeneralLinearGroup.exists_finite_quadratic_torus F p
  let f : Eˣ →* PSL(3,F) := (projection F).comp ((Matrix.SL3.blockEmbedding F).comp ρ)
  have hf : Function.Injective f := hp.comp ((Matrix.SL3.blockEmbedding_injective F).comp hρ)
  let e : Eˣ ≃* f.range := MonoidHom.ofInjective hf
  have hc : Nat.card f.range = Nat.card F ^ 2 - 1 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_units]
    exact congrArg (fun n => n - 1) (FiniteField.natCard_extension F p 2)
  refine ⟨f.range, e.isCyclic.mp inferInstance, hc, ?_⟩
  have hh := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
  rw [hg, mul_one, ← f.range.card_mul_index, hc] at hh
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card F ^ 2 - 1 by
    have hn : 1 < Nat.card F := Finite.one_lt_card
    exact Nat.sub_pos_of_lt (one_lt_pow₀ hn (by decide)))
  calc
    (Nat.card F ^ 2 - 1) * f.range.index =
        Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := hh
    _ = (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 * (Nat.card F ^ 3 - 1)) := by ring

theorem sylow_three_isCyclic (p : ℕ) [Fact p.Prime] [CharP F p]
    (hF : Nat.card F % 3 = 2) (P : Sylow 3 PSL(3,F)) : IsCyclic P := by
  obtain ⟨C, hc, _, hi⟩ := exists_cyclic_subgroup F p hF
  let _ := hc
  apply cyclic_sylow_of_cyclic_index C ?_ P
  rw [hi]
  have hmod : Nat.card F ^ 3 % 3 = 2 := by norm_num [Nat.pow_mod, hF]
  have hpos : 0 < Nat.card F ^ 3 := pow_pos Nat.card_pos _
  apply Nat.prime_three.not_dvd_mul <;> omega

end Matrix.PSL3.QuadraticThreeSylow

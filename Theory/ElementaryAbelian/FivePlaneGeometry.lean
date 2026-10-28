module

public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Lines and stabilizers in the elementary abelian five-plane

An elementary abelian group of order 25 has six subgroups of order five.
The order of the stabilizer of any such subgroup, for any subgroup of its
actual automorphism group, divides 80.

Identify subgroups with subspaces of the associated ZMod 5 vector space.
Projective cardinality counts the lines, and extension of a linear
isomorphism between lines proves transitivity of the full automorphism
group. Its order divides |GL₂(5)| = 480; orbit--stabilizer then gives the
required divisor 480 / 6 = 80. All subgroup actions are the pointwise maps
by the original multiplicative automorphisms.

This supplies the elementary geometry used in the final paragraph of
Aschbacher, *Sporadic Groups* (1994), Lemma 47.2, printed p.261.
-/

open scoped IsMulCommutative Pointwise LinearAlgebra.Projectivization
namespace IsElementaryAbelian.FivePlaneGeometry
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 5 E]
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private noncomputable def subspaceEquiv : Subgroup E ≃o Submodule (ZMod 5) (Additive E) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 5)

private theorem card_iff (L : Subgroup E) :
    Nat.card L = 5 ↔ Module.finrank (ZMod 5) (subspaceEquiv L) = 1 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 5) (V := subspaceEquiv L)
  change Nat.card L = _ at hc
  rw [Nat.card_zmod] at hc
  rw [hc]
  exact (Nat.pow_right_injective (by decide : 2 ≤ 5)).eq_iff (a := _) (b := 1)

/-- The elementary abelian group of order 25 has exactly six order-five subgroups. -/
public theorem card_lines (hE : Nat.card E = 25) :
    Nat.card {L : Subgroup E // Nat.card L = 5} = 6 := by
  let e := (Equiv.subtypeEquiv subspaceEquiv.toEquiv (card_iff (E := E))).trans
    (Projectivization.equivSubmodule (ZMod 5) (Additive E)).symm
  have hc := Projectivization.card' (ZMod 5) (Additive E)
  change Nat.card E = _ at hc
  rw [hE, Nat.card_zmod, ← Nat.card_congr e] at hc
  omega

private theorem lines_transitive (L M : Subgroup E) (hL : Nat.card L = 5)
    (hM : Nat.card M = 5) : ∃ a : MulAut E, L.map a.toMonoidHom = M := by
  let f : subspaceEquiv L ≃ₗ[ZMod 5] subspaceEquiv M :=
    LinearEquiv.ofFinrankEq _ _ ((card_iff L).mp hL |>.trans ((card_iff M).mp hM).symm)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  let a : MulAut E := MulEquiv.toAdditive.symm g.toAddEquiv
  refine ⟨a, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have he := hg ⟨Additive.ofMul y, hy⟩
    exact he ▸ (f ⟨Additive.ofMul y, hy⟩).property
  · intro hx
    let y := f.symm ⟨Additive.ofMul x, hx⟩
    refine ⟨y.val.toMul, y.property, ?_⟩
    have he := hg y
    rw [f.apply_symm_apply] at he
    exact he.symm

private theorem aut_orbit_card (hE : Nat.card E = 25) (L : Subgroup E) (hL : Nat.card L = 5) :
    Nat.card (MulAction.orbit (MulAut E) L) = 6 := by
  have he : MulAction.orbit (MulAut E) L = {M : Subgroup E | Nat.card M = 5} := by
    ext M
    constructor
    · rintro ⟨a, rfl⟩
      exact (Subgroup.card_map_of_injective a.injective).trans hL
    · intro hM
      exact lines_transitive L M hL hM
  rw [he]
  exact card_lines hE

private theorem aut_card_dvd (hE : Nat.card E = 25) : Nat.card (MulAut E) ∣ 480 := by
  obtain ⟨f, hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 5) (n := 2) E (by omega)
  have hd := Subgroup.card_dvd_of_injective f hf
  have hc : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) = 480 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ, ZMod.card]
  rwa [hc] at hd

private theorem full_stabilizer_dvd (hE : Nat.card E = 25) (L : Subgroup E)
    (hL : Nat.card L = 5) : Nat.card (MulAction.stabilizer (MulAut E) L) ∣ 80 := by
  have hc : Nat.card (MulAction.orbit (MulAut E) L) *
      Nat.card (MulAction.stabilizer (MulAut E) L) = Nat.card (MulAut E) := by
    rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (MulAut E) L)]
  rw [aut_orbit_card hE L hL] at hc
  have hd := aut_card_dvd hE
  rw [← hc] at hd
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 6) hd

/-- Under the literal pointwise subgroup-map action, every line stabilizer in
any subgroup of the automorphism group has order dividing 80. -/
public theorem stabilizer_card_dvd (hE : Nat.card E = 25) (H : Subgroup (MulAut E))
    (L : Subgroup E) (hL : Nat.card L = 5) : Nat.card (MulAction.stabilizer H L) ∣ 80 := by
  let f : MulAction.stabilizer H L →* MulAction.stabilizer (MulAut E) L :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : MulAction.stabilizer (MulAut E) L => z.val) he))
  exact (Subgroup.card_dvd_of_injective f hf).trans (full_stabilizer_dvd hE L hL)
end IsElementaryAbelian.FivePlaneGeometry

module
public import Theory.GroupTheory.WreathTwoSylowModel
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The cubic residual and its automizer in the two-triple wreath group

In the concrete `SL₂(2) ≀ C₂`, the subgroup of cubic base elements is
`O²`, has order nine, and is elementary abelian. Its centralizer is itself.
The checked Sylow dihedral embedding therefore acts faithfully on it;
counting the full conjugation image gives an actual `D₈` isomorphism.

This is the intrinsic model calculation used in Aschbacher--Smith 13.8.16(1),
printed p.952 (PDF p.969). It neither constructs the source subgroup `H₁`
nor assumes its dihedral automizer. The base subgroup and its conjugation
map are literal subgroups and homomorphisms, so quotient transports can
retain their connection to the original groups.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathModel
abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
abbrev C2 := Multiplicative (ZMod 2)
abbrev W := RegularWreathProduct SL2 C2
private instance : Fintype W := Fintype.ofEquiv ((C2 → SL2) × C2)
  (RegularWreathProduct.equivProd SL2 C2).symm
private instance : DecidableEq W := fun a b => decidable_of_iff
  (a.left = b.left ∧ a.right = b.right) RegularWreathProduct.ext_iff.symm

private theorem cube_mul : ∀ a b : SL2, a^3=1 → b^3=1 → (a*b)^3=1 := by
  decide +kernel

/-- The two independent cubic subgroups in the wreath base. -/
def cubicBase : Subgroup W where
  carrier := {x | x.right = 1 ∧ ∀ i, (x.left i)^3 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    exact ⟨by simp [ha.1, hb.1], fun i => cube_mul _ _ (ha.2 i) (hb.2 _)⟩
  inv_mem' := by
    intro a ha
    refine ⟨by simp [ha.1], ?_⟩
    intro i
    simpa only [RegularWreathProduct.inv_left, Pi.inv_apply, inv_pow, inv_one]
      using congrArg Inv.inv (ha.2 (a.right * i))

instance : cubicBase.Normal where
  conj_mem x hx g := by
    refine ⟨by simp [hx.1], ?_⟩
    intro i
    have he : (g*x*g⁻¹).left i =
        g.left i * x.left (g.right⁻¹*i) * (g.left i)⁻¹ := by simp [hx.1]
    rw [he, conj_pow, hx.2]
    simp

private instance : DecidablePred (fun x : W => x ∈ cubicBase) := fun x =>
  inferInstanceAs (Decidable (x.right=1 ∧ ∀ i, (x.left i)^3=1))

/-- Literal conjugation on the cubic base. -/
def action : W →* MulAut cubicBase := MulAut.conjNormal

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem centralizer_certificate : ∀ g : W,
    (∀ x : cubicBase, g * (x:W) * g⁻¹ = x) ↔ g ∈ cubicBase := by
  decide +kernel

/-- The kernel is the cubic base itself, computed in the actual wreath group. -/
theorem action_kernel : action.ker = cubicBase := by
  ext g
  change action g = 1 ↔ g ∈ cubicBase
  rw [← centralizer_certificate]
  constructor
  · intro h x
    exact congrArg (fun f : MulAut cubicBase => (f x : W)) h
  · intro h
    apply MulEquiv.ext
    intro x
    exact Subtype.ext (h x)

/-- The cubic base has order nine. -/
theorem cubicBase_card : Nat.card cubicBase = 9 := by
  let e : cubicBase ≃ (C2 → {x : SL2 // x^3=1}) := {
    toFun := fun x i => ⟨x.val.left i, x.property.2 i⟩
    invFun := fun f => ⟨⟨fun i => (f i).val, 1⟩, rfl, fun i => (f i).property⟩
    left_inv := fun x => by
      apply Subtype.ext
      exact RegularWreathProduct.ext rfl x.property.1.symm
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_fun]
  have hcard : Nat.card {x : SL2 // x^3=1} = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hcard]
  norm_num [Nat.card_eq_fintype_card]

private theorem wreath_card : Nat.card W = 72 := by
  rw [RegularWreathProduct.card]
  have h : Nat.card SL2 = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [h]
  norm_num [Nat.card_eq_fintype_card]

/-- Its full induced automorphism image has order eight. -/
theorem action_card : Nat.card action.range = 8 := by
  have h := action.ker.card_mul_index
  rw [Subgroup.index_ker, action_kernel, cubicBase_card, wreath_card] at h
  omega

private theorem cube_exponent : ∀ x : cubicBase, (x : W)^3 = 1 := by
  decide +kernel

instance : IsElementaryAbelian 3 cubicBase where
  is_comm := ⟨by decide +kernel⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    (fun x => Subtype.ext (cube_exponent x))

/-- The cubic residual has three-rank exactly two. -/
theorem cubicBase_threeRank : primeRank 3 cubicBase = 2 := by
  apply le_antisymm (IsElementaryAbelian.primeRank_le_of_card_le cubicBase (by
    rw [cubicBase_card]; decide))
  let : IsElementaryAbelian 3 (⊤ : Subgroup cubicBase) := {
    is_comm := ⟨fun a b => Subtype.ext (mul_comm a.val b.val)⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => Subtype.ext (Subtype.ext (cube_exponent x.val))) }
  have hr := IsElementaryAbelian.primeRank_ge_of_card (p := 3) (n := 2)
    (⊤ : Subgroup cubicBase) (by simpa using cubicBase_card)
  exact hr

/-- The cubic base is the two-residual, not the two-core. -/
theorem twoResidual_eq : pResidual 2 W = cubicBase := by
  apply le_antisymm
  · have hi : cubicBase.index = 8 := by
      rw [← action_kernel, Subgroup.index_ker, action_card]
    have hp : IsPGroup 2 (W ⧸ cubicBase) := IsPGroup.of_card (n := 3) (by
      change cubicBase.index = 8
      exact hi)
    exact sInf_le ⟨inferInstance, hp⟩
  · intro x hx
    exact mem_pResidual_of_orderOf_coprime
      ((show Nat.Coprime 2 3 by decide).of_dvd_right
        (orderOf_dvd_of_pow_eq_one (cube_exponent ⟨x, hx⟩)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem dihedral_detected : ∀ d : DihedralGroup 4,
    wreathTwoDihedralHom d ∈ cubicBase → d = 1 := by
  decide +kernel

/-- The standard dihedral subgroup acts faithfully on the two cubic axes. -/
theorem dihedral_action_injective : Function.Injective (action.comp wreathTwoDihedralHom) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro d hd
  apply dihedral_detected d
  rw [← action_kernel]
  exact hd

/-- The actual induced automorphism group of the cubic base is dihedral of order eight. -/
noncomputable def actionEquivDihedral : action.range ≃* DihedralGroup 4 := by
  let f : DihedralGroup 4 →* action.range :=
    (action.comp wreathTwoDihedralHom).codRestrict action.range (fun d => ⟨_, rfl⟩)
  have hf : Function.Injective f := by
    intro x y h
    exact dihedral_action_injective (congrArg Subtype.val h)
  exact (MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf, by rw [DihedralGroup.nat_card, action_card]⟩)).symm

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathModel
end

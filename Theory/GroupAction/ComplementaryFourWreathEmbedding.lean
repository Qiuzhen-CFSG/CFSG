module

public import Theory.GroupAction.ComplementaryFourWreathAction
import all Theory.GroupAction.ComplementaryFourWreathAction

/-!
# Embedding the actor of two complementary four-groups

A faithful action permuting two complementary four-groups embeds in the
binary-plane wreath group. The coordinate construction does not require
the actor to have order 72; that hypothesis is needed only to make the
embedding surjective.
-/

open scoped IsMulCommutative
namespace ComplementaryFourWreathAction

public theorem exists_injective_wreath_of_complementary_four
    {G V : Type*} [Group G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (U0 U1 : Subgroup V) (hcompl : IsCompl U0 U1)
    (hcard0 : Nat.card U0 = 4) (hcard1 : Nat.card U1 = 4)
    (hfaithful : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hperm : ∀g : G,
      (U0.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U0 ∧
       U1.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U1) ∨
      (U0.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U1 ∧
       U1.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U0)) :
    ∃ φ : G →* RegularWreathProduct
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)),
      Function.Injective φ := by
  classical
  let _ : IsElementaryAbelian 2 U0 := elementary_subgroup U0
  let _ : IsElementaryAbelian 2 U1 := elementary_subgroup U1
  obtain ⟨e0,_⟩ := FourGroupMatrixCoordinates.exists_four_group_matrix_coordinates hcard0
  obtain ⟨e1,_⟩ := FourGroupMatrixCoordinates.exists_four_group_matrix_coordinates hcard1
  obtain ⟨e,he0,he1⟩ := exists_pair_coordinates U0 U1 hcompl e0 e1
  let _ : FaithfulSMul G V := by
    rw [faithfulSMul_iff]
    intro g hg
    have hm : g ∈ fixingSubgroup G (Set.univ : Set V) :=
      (mem_fixingSubgroup_iff G).mpr (fun v _ => hg v)
    simpa [hfaithful] using hm
  let K := Multiplicative (Fin 2 → ZMod 2)
  let D := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := FourGroupMatrixCoordinates.naturalAction_faithful
  let _ := RegularWreathProduct.functionModule D (Multiplicative (ZMod 2)) K
  let _ := RegularWreathProduct.functionModule_faithful D (Multiplicative (ZMod 2)) K
  let eV := e.trans (pairFunction K)
  have hex (g : G) : ∃w : RegularWreathProduct D (Multiplicative (ZMod 2)),
      ∀v, eV (g • v) = w • eV v :=
    exists_wreath_action e FourGroupMatrixCoordinates.naturalAction_surjective g
      (conjugate_preserves_or_swaps U0 U1 e he0 he1 g (hperm g))
  choose w hw using hex
  have heq {a b : RegularWreathProduct D (Multiplicative (ZMod 2))}
      (h : ∀v : V, a • eV v = b • eV v) : a = b := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Multiplicative (ZMod 2) → K)
    intro v
    obtain ⟨v,rfl⟩ := eV.surjective v
    exact h v
  let φ : G →* RegularWreathProduct D (Multiplicative (ZMod 2)) := {
    toFun := w
    map_one' := heq (fun v => by rw [←hw,one_smul,one_smul])
    map_mul' := fun a b => heq (fun v => by rw [←hw,mul_smul,hw,hw,mul_smul]) }
  refine ⟨φ,?_⟩
  intro a b hab
  apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
  intro v
  apply eV.injective
  rw [hw,hw]
  exact congrArg (fun z => z • eV v) hab

end ComplementaryFourWreathAction

module

public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The two intrinsic cubic counts in the binary linear model

A coordinate three-cycle fixes a line on the natural module. Conjugacy of
Sylow three-subgroups transports that line to every cubic, and duality gives
the same fixed dimension on the dual. Their sum therefore has four fixed
vectors. The centralizer of the cycle in SL₃(2) is its cyclic subgroup.
Inverse transpose fixes the cycle; the inner/graph decomposition identifies
its automorphism centralizer with two copies of that subgroup. Sylow
conjugacy in the actual automorphism group transports the order six.

Finite checks are confined to the representative's matrices and eight
natural vectors; conjugacy supplies the general case.
Source: Aschbacher–Smith, the H-centralizer calculation preceding 15.3.60,
combined manuscript (1 March 2004), printed p.1150.
-/

public section

open Matrix Subgroup Representation Representation.BinaryOffender BinaryLinearThree
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.CubicModel

private def cycle : Matrix.PSL3Two.SL := ⟨!![0,0,1;1,0,0;0,1,0], by decide⟩
private lemma cycle_order : orderOf cycle = 3 :=
  orderOf_eq_prime (by decide : cycle ^ 3 = 1) (by decide : cycle ≠ 1)
private lemma natural_test : ∀ v : Vector, W cycle v = v ↔ (fun _ => v 0) = v := by decide
private noncomputable def naturalFixedEquiv : fixedSpace W (zpowers cycle) ≃ₗ[ZMod 2] ZMod 2 where
  toFun v := v.val 0
  invFun a := ⟨fun _ => a, by rw [mem_fixedSpace_zpowers_iff, natural_test]⟩
  left_inv v := Subtype.ext ((natural_test v.val).mp ((mem_fixedSpace_zpowers_iff _ _ _).mp v.property))
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private lemma centralizer_test : ∀ g : Matrix.PSL3Two.SL,
    g * cycle = cycle * g ↔ g = 1 ∨ g = cycle ∨ g = cycle ^ 2 := by decide +kernel

private lemma cycle_centralizer : centralizer ({cycle} : Set Matrix.PSL3Two.SL) = zpowers cycle := by
  apply le_antisymm
  · intro g hg
    rcases (centralizer_test g).mp (mem_centralizer_singleton_iff.mp hg) with rfl | rfl | rfl
    · exact one_mem _
    · exact mem_zpowers cycle
    · exact pow_mem (mem_zpowers cycle) 2
  · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
private lemma cycle_centralizer_card : Nat.card (centralizer ({cycle} : Set Matrix.PSL3Two.SL)) = 3 := by
  rw [cycle_centralizer, Nat.card_zpowers, cycle_order]
private noncomputable def cubicSylow (X : Subgroup Matrix.PSL3Two.SL) (hX : Nat.card X = 3) :
    Sylow 3 Matrix.PSL3Two.SL :=
  (IsPGroup.of_card (n := 1) (by simpa using hX)).toSylow (by
    have hi := X.card_mul_index
    rw [hX, Matrix.PSL3Two.card_SL] at hi
    have hind : X.index = 56 := by omega
    rw [hind]
    decide)
private lemma natural_fixed_card (X : Subgroup Matrix.PSL3Two.SL) (hX : Nat.card X = 3) :
    Nat.card (fixedSpace W X) = 2 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Matrix.PSL3Two.SL
    (cubicSylow (zpowers cycle) (by rw [Nat.card_zpowers, cycle_order])) (cubicSylow X hX)
  have he : (zpowers cycle).map (MulAut.conj g).toMonoidHom = X :=
    congrArg (fun T : Sylow 3 Matrix.PSL3Two.SL => (T : Subgroup Matrix.PSL3Two.SL)) hg
  rw [← he, ← Nat.card_congr (fixedSpaceConjEquiv W (zpowers cycle) g).toEquiv,
    Nat.card_congr naturalFixedEquiv.toEquiv, Nat.card_zmod]
private lemma natural_fixed_finrank (X : Subgroup Matrix.PSL3Two.SL) (hX : Nat.card X = 3) :
    Module.finrank (ZMod 2) (fixedSpace W X) = 1 := by
  have h := natural_fixed_card X hX
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) (h.trans (pow_one 2).symm)
private lemma dual_fixed_card (X : Subgroup Matrix.PSL3Two.SL) (hX : Nat.card X = 3) :
    Nat.card (fixedSpace W.dual X) = 2 := by
  obtain ⟨g,hg⟩ := X.isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_of_prime_card hX)
  have hd := fixedCodim_zpowers_dual W g
  rw [hg] at hd
  have h1 := fixedCodim_add_finrank W X
  have h2 := fixedCodim_add_finrank W.dual X
  rw [natural_fixed_finrank X hX] at h1
  rw [Subspace.dual_finrank_eq] at h2
  have hf : Module.finrank (ZMod 2) (fixedSpace W.dual X) = 1 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hf, pow_one]
private noncomputable def pairedFixedEquiv (X : Subgroup Matrix.PSL3Two.SL) :
    fixedSpace (W.prod W.dual) X ≃ (fixedSpace W X × fixedSpace W.dual X) where
  toFun v := (⟨v.val.1, fun g => congrArg Prod.fst (v.property g)⟩,
    ⟨v.val.2, fun g => congrArg Prod.snd (v.property g)⟩)
  invFun v := ⟨(v.1.val,v.2.val), fun g => Prod.ext (v.1.property g) (v.2.property g)⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-- Every cubic fixes exactly four vectors in the natural-plus-dual module. -/
lemma paired_fixed_card (X : Subgroup Matrix.PSL3Two.SL) (hX : Nat.card X = 3) :
    Nat.card (fixedSpace (W.prod W.dual) X) = 4 := by
  rw [Nat.card_congr (pairedFixedEquiv X), Nat.card_prod, natural_fixed_card X hX,
    dual_fixed_card X hX]

open BinaryLinearThree.AutomorphismAction
private lemma conj_injective : Function.Injective (MulAut.conj : Matrix.PSL3Two.SL →* MulAut Matrix.PSL3Two.SL) :=
  MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
private lemma graph_cycle : graph cycle = cycle := by
  change cycle⁻¹.transpose = cycle
  have hi : cycle⁻¹ = cycle ^ 2 := inv_eq_of_mul_eq_one_right (by decide)
  rw [hi]
  decide
private lemma mem_aut_centralizer (a : MulAut Matrix.PSL3Two.SL) :
    a ∈ centralizer ({MulAut.conj cycle} : Set _) ↔ a cycle = cycle := by
  have he : a * MulAut.conj cycle = MulAut.conj (a cycle) * a := by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [mem_centralizer_singleton_iff, he, mul_right_cancel_iff, conj_injective.eq_iff]
private def standardForm (x : Bool × Matrix.PSL3Two.SL) : MulAut Matrix.PSL3Two.SL :=
  if x.1 then MulAut.conj x.2 * graph else MulAut.conj x.2
private lemma standardForm_injective : Function.Injective standardForm := by
  rintro ⟨b,g⟩ ⟨c,h⟩ he
  cases b <;> cases c
  · have hh : g = h := conj_injective he
    subst h
    rfl
  · have hh : graph = MulAut.conj (h⁻¹ * g) := by
      change MulAut.conj g = MulAut.conj h * graph at he
      rw [map_mul, map_inv, he]
      group
    exact False.elim (graph_not_inner (hh ▸ ⟨h⁻¹ * g, rfl⟩))
  · have hh : graph = MulAut.conj (g⁻¹ * h) := by
      change MulAut.conj g * graph = MulAut.conj h at he
      rw [map_mul, map_inv, ← he]
      group
    exact False.elim (graph_not_inner (hh ▸ ⟨g⁻¹ * h, rfl⟩))
  · have hh := conj_injective (mul_right_cancel (show MulAut.conj g * graph = MulAut.conj h * graph from he))
    subst h
    rfl
private lemma standardForm_centralizes (b : Bool) (g : Matrix.PSL3Two.SL) :
    standardForm (b,g) ∈ centralizer ({MulAut.conj cycle} : Set _) ↔
      g ∈ centralizer ({cycle} : Set _) := by
  rw [mem_aut_centralizer, mem_centralizer_singleton_iff]
  cases b <;> simp only [standardForm, Bool.false_eq_true, ↓reduceIte, MulAut.mul_apply,
    graph_cycle, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
private noncomputable def autCentralizerEquiv :
    (Bool × centralizer ({cycle} : Set Matrix.PSL3Two.SL)) ≃
      centralizer ({MulAut.conj cycle} : Set (MulAut Matrix.PSL3Two.SL)) := by
  let f : (Bool × centralizer ({cycle} : Set Matrix.PSL3Two.SL)) →
      centralizer ({MulAut.conj cycle} : Set (MulAut Matrix.PSL3Two.SL)) := fun x =>
    ⟨standardForm (x.1,x.2.val), (standardForm_centralizes x.1 x.2.val).mpr x.2.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hh := standardForm_injective (congrArg Subtype.val h)
    exact Prod.ext (congrArg (fun t : Bool × Matrix.PSL3Two.SL => t.1) hh)
      (Subtype.ext (congrArg (fun t : Bool × Matrix.PSL3Two.SL => t.2) hh))
  · intro a
    by_cases ha : a.val ∈ MulAut.innerSubgroup Matrix.PSL3Two.SL
    · obtain ⟨g,hg⟩ := ha
      have hm : standardForm (false,g) ∈ centralizer ({MulAut.conj cycle} : Set _) := by
        change MulAut.conj g ∈ _
        rw [hg]
        exact a.property
      exact ⟨(false,⟨g,(standardForm_centralizes false g).mp hm⟩), Subtype.ext hg⟩
    · obtain ⟨g,hg⟩ := outer_eq_inner_graph a.val ha
      have hm : standardForm (true,g) ∈ centralizer ({MulAut.conj cycle} : Set _) := by
        change MulAut.conj g * graph ∈ _
        rw [← hg]
        exact a.property
      exact ⟨(true,⟨g,(standardForm_centralizes true g).mp hm⟩), Subtype.ext hg.symm⟩
private lemma aut_cycle_centralizer_card :
    Nat.card (centralizer ({MulAut.conj cycle} : Set (MulAut Matrix.PSL3Two.SL))) = 6 := by
  rw [← Nat.card_congr autCentralizerEquiv, Nat.card_prod, cycle_centralizer_card, Nat.card_eq_fintype_card]
  decide
/-- An actual group equivalence transports the entire subgroup centralizer. -/
lemma map_centralizer_equiv {A B : Type*} [_root_.Group A] [_root_.Group B]
    (X : Subgroup A) (e : A ≃* B) :
    (centralizer (X : Set A)).map e.toMonoidHom = centralizer (X.map e.toMonoidHom : Set B) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)
/-- Every subgroup of order three has centralizer of order six in Aut(SL₃(2)). -/
lemma aut_centralizer_card (X : Subgroup (MulAut Matrix.PSL3Two.SL)) (hX : Nat.card X = 3) :
    Nat.card (centralizer (X : Set (MulAut Matrix.PSL3Two.SL))) = 6 := by
  have hc : Nat.card (zpowers (MulAut.conj cycle)) = 3 := by
    rw [Nat.card_zpowers, orderOf_injective _ conj_injective, cycle_order]
  have hAut : Nat.card (MulAut Matrix.PSL3Two.SL) = 336 :=
    (Nat.card_congr (MulAut.congr Matrix.PSL3Two.equiv).toEquiv).trans Matrix.PSL3Two.Automorphisms.card_aut
  let syl (K : Subgroup (MulAut Matrix.PSL3Two.SL)) (hK : Nat.card K = 3) :
      Sylow 3 (MulAut Matrix.PSL3Two.SL) :=
    (IsPGroup.of_card (n := 1) (by simpa using hK)).toSylow (by
      have hi := K.card_mul_index
      rw [hK, hAut] at hi
      have hind : K.index = 112 := by omega
      rw [hind]
      decide)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (MulAut Matrix.PSL3Two.SL)
    (syl (zpowers (MulAut.conj cycle)) hc) (syl X hX)
  have he : (zpowers (MulAut.conj cycle)).map (MulAut.conj g).toMonoidHom = X :=
    congrArg (fun T : Sylow 3 (MulAut Matrix.PSL3Two.SL) => (T : Subgroup (MulAut Matrix.PSL3Two.SL))) hg
  rw [← he, ← map_centralizer_equiv, card_map_of_injective (MulAut.conj g).injective,
    zpowers_eq_closure, centralizer_closure, aut_cycle_centralizer_card]
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.CubicModel

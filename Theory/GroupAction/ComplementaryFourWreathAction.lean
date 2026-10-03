module

public import Theory.GroupAction.RegularWreathFunctionModule
public import Theory.Representation.FourGroupMatrixCoordinates
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Recognizing the natural action on two complementary four-groups

A faithful action of a group of order 72 on an elementary abelian two-group,
permuting two complementary subgroups of order four, is the natural action of
SL₂(2) wr C₂. The group and module equivalences in the conclusion are compatible
with the supplied action, as expressed by the literal matrix coordinate formula.

Multiplication in the complementary subgroups gives product coordinates. An
automorphism preserving the two axes is a pair of automorphisms of a four-group;
one swapping the axes is such a pair followed by the swap. Every automorphism
of a four-group is a natural SL₂(2) matrix. These observations produce a wreath
element with the required action for every actor. Faithfulness of the standard
wreath action makes these choices a homomorphism; faithfulness of the supplied
action makes it injective. Both groups have order 72, so it is an equivalence.

This is the intrinsic imprimitive-module recognition needed for Stellmacher
(1.7) and the rank-two wreath conclusion in (9.3). Only the complementary
four-group decomposition, the actual action, and its faithfulness are used.
-/

open scoped IsMulCommutative
namespace ComplementaryFourWreathAction

private theorem aut_prod_of_preserving {K : Type*} [Group K]
    (f : MulAut (K × K))
    (h0 : ∀v : K, (f (v, 1)).2 = 1)
    (h1 : ∀v : K, (f (1, v)).1 = 1) :
    ∃a b : MulAut K, ∀v : K × K, f v = (a v.1, b v.2) := by
  let a : K →* K := (MonoidHom.fst K K).comp (f.toMonoidHom.comp (MonoidHom.inl K K))
  let b : K →* K := (MonoidHom.snd K K).comp (f.toMonoidHom.comp (MonoidHom.inr K K))
  have hf (v : K × K) : f v = (a v.1, b v.2) := by
    have hv : v = (v.1, 1) * (1, v.2) := by ext <;> simp
    calc
      f v = f (v.1, 1) * f (1, v.2) := by rw [← map_mul, ← hv]
      _ = (a v.1, b v.2) := by ext <;> simp [a, b, h0, h1]
  have ha : Function.Bijective a := by
    constructor
    · intro x y hxy
      have hh : f (x, 1) = f (y, 1) := by simpa [hf] using congrArg (fun k : K => (k, (1 : K))) hxy
      exact congrArg Prod.fst (f.injective hh)
    · intro x
      obtain ⟨v,hv⟩ := f.surjective (x,1)
      exact ⟨v.1, by simpa [hf] using congrArg Prod.fst hv⟩
  have hb : Function.Bijective b := by
    constructor
    · intro x y hxy
      have hh : f (1, x) = f (1, y) := by simpa [hf] using congrArg (fun k : K => ((1 : K), k)) hxy
      exact congrArg Prod.snd (f.injective hh)
    · intro x
      obtain ⟨v,hv⟩ := f.surjective (1,x)
      exact ⟨v.2, by simpa [hf] using congrArg Prod.snd hv⟩
  exact ⟨MulEquiv.ofBijective a ha, MulEquiv.ofBijective b hb, hf⟩

private def pairFunction (K : Type*) [Group K] : (K × K) ≃* (Multiplicative (ZMod 2) → K) where
  toFun v i := if i = 1 then v.1 else v.2
  invFun v := (v 1, v (Multiplicative.ofAdd 1))
  left_inv v := by simp
  right_inv v := by
    funext i
    have hi : ∀i : Multiplicative (ZMod 2), i = 1 ∨ i = Multiplicative.ofAdd 1 := by decide
    rcases hi i with rfl | rfl <;> simp [show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 from by decide]
  map_mul' v w := by
    funext i
    by_cases hi : i = 1 <;> simp [hi]

private theorem exists_pair_coordinates {V K : Type*} [Group V] [IsMulCommutative V]
    [Group K] (U0 U1 : Subgroup V) (hc : IsCompl U0 U1)
    (e0 : U0 ≃* K) (e1 : U1 ≃* K) :
    ∃e : V ≃* (K × K),
      (∀v, v ∈ U0 ↔ (e v).2 = 1) ∧ (∀v, v ∈ U1 ↔ (e v).1 = 1) := by
  let f := U0.subtype.noncommCoprod U1.subtype (fun _ _ => Commute.all _ _)
  have hfinj : Function.Injective f := Subgroup.mul_injective_of_disjoint hc.disjoint
  have hfsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    exact hc.sup_eq_top
  let ef := MulEquiv.ofBijective f ⟨hfinj,hfsurj⟩
  let e := ef.symm.trans (e0.prodCongr e1)
  have he (a : U0) (b : U1) : e ((a : V) * (b : V)) = (e0 a,e1 b) := by
    exact congrArg (e0.prodCongr e1) (ef.symm_apply_apply (a,b))
  refine ⟨e, ?_, ?_⟩
  · intro v
    obtain ⟨⟨a,b⟩,rfl⟩ := hfsurj v
    change ((a : V) * (b : V) ∈ U0 ↔ (e ((a : V) * (b : V))).2 = 1)
    rw [he]
    change ((a : V) * (b : V) ∈ U0 ↔ e1 b = 1)
    rw [e1.map_eq_one_iff]
    constructor
    · intro h
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hc.disjoint (by simpa using U0.mul_mem (U0.inv_mem a.property) h) b.property
    · intro h
      simp [h]
  · intro v
    obtain ⟨⟨a,b⟩,rfl⟩ := hfsurj v
    change ((a : V) * (b : V) ∈ U1 ↔ (e ((a : V) * (b : V))).1 = 1)
    rw [he]
    change ((a : V) * (b : V) ∈ U1 ↔ e0 a = 1)
    rw [e0.map_eq_one_iff]
    constructor
    · intro h
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hc.disjoint a.property (by simpa using U1.mul_mem h (U1.inv_mem b.property))
    · intro h
      simp [h]

private theorem aut_prod_of_swapping {K : Type*} [Group K]
    (f : MulAut (K × K))
    (h0 : ∀v : K, (f (v, 1)).1 = 1)
    (h1 : ∀v : K, (f (1, v)).2 = 1) :
    ∃a b : MulAut K, ∀v : K × K, f v = (a v.2, b v.1) := by
  let s : MulAut (K × K) := MulEquiv.prodComm
  obtain ⟨a,b,h⟩ := aut_prod_of_preserving (s.trans f) h1 h0
  refine ⟨a,b,?_⟩
  intro v
  simpa [s] using h (v.2,v.1)

private theorem conjugate_preserves_or_swaps {G V K : Type*} [Group G] [Group V]
    [Group K] [MulDistribMulAction G V]
    (U0 U1 : Subgroup V) (e : V ≃* (K × K))
    (h0 : ∀v, v ∈ U0 ↔ (e v).2 = 1)
    (h1 : ∀v, v ∈ U1 ↔ (e v).1 = 1)
    (g : G)
    (hperm :
      (U0.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U0 ∧
       U1.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U1) ∨
      (U0.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U1 ∧
       U1.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U0)) :
    (∃a b : MulAut K, ∀v : V, e (g • v) = (a (e v).1,b (e v).2)) ∨
    (∃a b : MulAut K, ∀v : V, e (g • v) = (a (e v).2,b (e v).1)) := by
  let f : MulAut (K × K) := e.symm.trans ((MulDistribMulAction.toMulAut G V g).trans e)
  have hm {A B : Subgroup V}
      (he : A.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = B)
      {v : V} (hv : v ∈ A) : g • v ∈ B := by
    rw [← he]
    exact ⟨v,hv,rfl⟩
  rcases hperm with hh | hh
  · obtain ⟨a,b,h⟩ := aut_prod_of_preserving f
      (fun v => (h0 _).mp (hm hh.1 ((h0 _).mpr (by simp))))
      (fun v => (h1 _).mp (hm hh.2 ((h1 _).mpr (by simp))))
    exact Or.inl ⟨a,b,fun v => by simpa [f] using h (e v)⟩
  · obtain ⟨a,b,h⟩ := aut_prod_of_swapping f
      (fun v => (h1 _).mp (hm hh.1 ((h0 _).mpr (by simp))))
      (fun v => (h0 _).mp (hm hh.2 ((h1 _).mpr (by simp))))
    exact Or.inr ⟨a,b,fun v => by simpa [f] using h (e v)⟩

private theorem exists_wreath_action {G V K D : Type*} [Group G] [Group V]
    [Group K] [Group D] [MulDistribMulAction G V] [MulDistribMulAction D K]
    (e : V ≃* (K × K))
    (hD : ∀a : MulAut K, ∃d : D, ∀v, d • v = a v)
    (g : G)
    (hperm :
      (∃a b : MulAut K, ∀v : V, e (g • v) = (a (e v).1,b (e v).2)) ∨
      (∃a b : MulAut K, ∀v : V, e (g • v) = (a (e v).2,b (e v).1))) :
    letI := RegularWreathProduct.functionModule D (Multiplicative (ZMod 2)) K
    ∃w : RegularWreathProduct D (Multiplicative (ZMod 2)),
      ∀v, pairFunction K (e (g • v)) = w • pairFunction K (e v) := by
  let _ := RegularWreathProduct.functionModule D (Multiplicative (ZMod 2)) K
  have hcases : ∀i : Multiplicative (ZMod 2), i = 1 ∨ i = Multiplicative.ofAdd 1 := by decide
  have ht : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
  rcases hperm with ⟨a,b,h⟩ | ⟨a,b,h⟩
  · obtain ⟨da,hda⟩ := hD a
    obtain ⟨db,hdb⟩ := hD b
    refine ⟨⟨(fun i => if i = 1 then da else db), 1⟩,?_⟩
    intro v
    funext i
    rw [RegularWreathProduct.functionModule_smul_apply, h]
    rcases hcases i with rfl | rfl <;> simp [pairFunction, ht, hda, hdb]
  · obtain ⟨da,hda⟩ := hD a
    obtain ⟨db,hdb⟩ := hD b
    refine ⟨⟨(fun i => if i = 1 then da else db), Multiplicative.ofAdd 1⟩,?_⟩
    intro v
    funext i
    rw [RegularWreathProduct.functionModule_smul_apply, h]
    have htinv : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide
    have htt : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases hcases i with rfl | rfl <;> simp [pairFunction, ht, htinv, htt, hda, hdb]

private theorem equiv_wreath_of_action {G V K D : Type*} [Group G] [Group V]
    [Group K] [Group D] [Finite G] [Finite D] [Nontrivial K]
    [MulDistribMulAction G V] [MulDistribMulAction D K]
    [FaithfulSMul G V] [FaithfulSMul D K]
    (e : V ≃* (K × K))
    (hD : ∀a : MulAut K, ∃d : D, ∀v, d • v = a v)
    (hcard : Nat.card G = Nat.card (RegularWreathProduct D (Multiplicative (ZMod 2))))
    (hperm : ∀g : G,
      (∃a b : MulAut K, ∀v : V, e (g • v) = (a (e v).1,b (e v).2)) ∨
      (∃a b : MulAut K, ∀v : V, e (g • v) = (a (e v).2,b (e v).1))) :
    letI := RegularWreathProduct.functionModule D (Multiplicative (ZMod 2)) K
    ∃eG : G ≃* RegularWreathProduct D (Multiplicative (ZMod 2)),
      ∃eV : V ≃* (Multiplicative (ZMod 2) → K),
        ∀g v, eV (g • v) = eG g • eV v := by
  classical
  let _ := RegularWreathProduct.functionModule D (Multiplicative (ZMod 2)) K
  let _ := RegularWreathProduct.functionModule_faithful D (Multiplicative (ZMod 2)) K
  let eV := e.trans (pairFunction K)
  have hex (g : G) : ∃w : RegularWreathProduct D (Multiplicative (ZMod 2)),
      ∀v, eV (g • v) = w • eV v := exists_wreath_action e hD g (hperm g)
  choose w hw using hex
  have heq {a b : RegularWreathProduct D (Multiplicative (ZMod 2))}
      (h : ∀v : V, a • eV v = b • eV v) : a = b := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Multiplicative (ZMod 2) → K)
    intro v
    obtain ⟨v,rfl⟩ := eV.surjective v
    exact h v
  let φ : G →* RegularWreathProduct D (Multiplicative (ZMod 2)) :=
    { toFun := w
      map_one' := heq (fun v => by rw [← hw, one_smul, one_smul])
      map_mul' := fun a b => heq (fun v => by rw [← hw, mul_smul, hw, hw, mul_smul]) }
  have hinj : Function.Injective φ := by
    intro a b hab
    apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
    intro v
    apply eV.injective
    rw [hw, hw]
    exact congrArg (fun z => z • eV v) hab
  have hbij := (Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj,hcard⟩
  exact ⟨MulEquiv.ofBijective φ hbij,eV,hw⟩

private theorem elementary_subgroup {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (U : Subgroup V) : IsElementaryAbelian 2 U := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro u
  apply Subtype.ext
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 V) u

public theorem equiv_natural_wreath_of_complementary_four
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (U0 U1 : Subgroup V) (hcompl : IsCompl U0 U1)
    (hcard0 : Nat.card U0 = 4) (hcard1 : Nat.card U1 = 4)
    (hfaithful : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcardG : Nat.card G = 72)
    (hperm : ∀g : G,
      (U0.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U0 ∧
       U1.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U1) ∨
      (U0.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U1 ∧
       U1.map (MulDistribMulAction.toMulAut G V g).toMonoidHom = U0)) :
    ∃ eG : G ≃* RegularWreathProduct
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)),
      ∃ eV : V ≃* (Multiplicative (ZMod 2) → Multiplicative (Fin 2 → ZMod 2)),
        ∀g v i, eV (g • v) i = Multiplicative.ofAdd
          (Matrix.mulVec ((eG g).left i).1
            (Multiplicative.toAdd (eV v ((eG g).right⁻¹ * i)))) := by
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
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := FourGroupMatrixCoordinates.naturalAction_faithful
  have hc : Nat.card G = Nat.card (RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))) := by
    obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    rw [hcardG, RegularWreathProduct.card, Nat.card_congr eSL.toEquiv, Nat.card_perm]
    norm_num [Nat.factorial]
  obtain ⟨eG,eV,h⟩ := equiv_wreath_of_action e
    FourGroupMatrixCoordinates.naturalAction_surjective hc
    (fun g => conjugate_preserves_or_swaps U0 U1 e he0 he1 g (hperm g))
  exact ⟨eG,eV,fun g v i => congrFun (h g v) i⟩

end ComplementaryFourWreathAction

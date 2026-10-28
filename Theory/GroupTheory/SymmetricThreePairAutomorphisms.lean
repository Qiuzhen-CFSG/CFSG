module
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupAction.RegularWreathFunctionModule
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Automorphisms of a symmetric-three pair

A normal S₃ subgroup of S₃ × S₃ is a coordinate factor. An automorphism
therefore preserves or exchanges the factors; factor-preserving automorphisms
are inner. The faithful coordinate action realizes the full automorphism
group as the literal regular wreath product S₃ ≀ C₂. The inner subgroup has
no intermediate overgroups. No enumeration of the whole automorphism type
is used.

This supplies the two-group extension calculation in Aschbacher--Smith,
15.1.22(3), printed pp.1099--1100.
-/

public section
set_option linter.style.haveILetI false
open Subgroup
namespace Theory.GroupTheory.SymmetricThreePairAutomorphisms
abbrev D := Equiv.Perm (Fin 3)
abbrev X := D × D
abbrev Q := Multiplicative (ZMod 2)
abbrev W := RegularWreathProduct D Q
private def A : Subgroup X := (⊤ : Subgroup D).prod ⊥
private def axisEquiv : A ≃* D where
  toFun x := x.val.1
  invFun x := ⟨(x,1),by exact ⟨mem_top _,rfl⟩⟩
  left_inv x := by apply Subtype.ext; exact Prod.ext rfl x.property.2.symm
  right_inv x := rfl
  map_mul' x y := rfl

/-- Every automorphism is inner, possibly followed by exchange of the factors. -/
theorem inner_or_swap (a : MulAut X) :
    (∃ x : X, a = MulAut.conj x) ∨
      ∃ x : X, a = (MulAut.conj x) * MulEquiv.prodComm := by
  letI : A.Normal := inferInstanceAs (((⊤ : Subgroup D).prod ⊥).Normal)
  let C := A.map a.toMonoidHom
  letI : C.Normal := Normal.map inferInstance _ a.surjective
  have hc := PermThreeProduct.normal_subgroup_eq_factor C
    ((a.subgroupMap A).symm.trans axisEquiv)
  have preserve (f : MulAut X) (hA : A.map f.toMonoidHom = A) :
      ∃ x : X, f = MulAut.conj x := by
    have hfirst (x : D) : (f (x,1)).2 = 1 := by
      have hh := hA ▸ mem_map_of_mem f.toMonoidHom (show (x,1) ∈ A from ⟨mem_top _,rfl⟩)
      exact hh.2
    have hsecond (x : D) : (f (1,x)).1 = 1 := by
      apply NormalSymmetricThreePairRank.symmetricThree_center_trivial
      intro y
      have hy : (y,1) ∈ A.map f.toMonoidHom := hA.symm ▸ (show (y,1) ∈ A from ⟨mem_top _,rfl⟩)
      obtain ⟨z,hz,hzy⟩ := hy
      change f z = (y,1) at hzy
      have hz' : z = (z.1,1) := Prod.ext rfl hz.2
      have hcomm : z * (1,x) = (1,x) * z := by rw [hz']; simp
      have hm := congrArg (fun z : X => (f z).1) hcomm
      rw [map_mul,map_mul,hzy] at hm
      exact hm
    exact NormalSymmetricThreePairRank.pair_aut_inner f hfirst hsecond
  rcases hc with hc | hc
  · exact Or.inl (preserve a hc)
  · right
    let f : MulAut X := MulEquiv.prodComm * a
    change A.map a.toMonoidHom = (⊥ : Subgroup D).prod ⊤ at hc
    have hf : A.map f.toMonoidHom = A := by
      change A.map (MulEquiv.prodComm.toMonoidHom.comp a.toMonoidHom) = A
      rw [←map_map,hc]
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact ⟨mem_top _,hy.1⟩
      · intro hx
        exact ⟨(x.2,x.1),⟨hx.2,mem_top _⟩,rfl⟩
    obtain ⟨x,hx⟩ := preserve f hf
    refine ⟨(x.2,x.1),?_⟩
    apply MulEquiv.ext
    intro y
    have hh := congrArg Prod.swap (DFunLike.congr_fun hx y)
    exact hh

/-- The conjugation map of the pair is faithful. -/
theorem pair_conj_injective : Function.Injective (MulAut.conj : X →* MulAut X) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (MulAut.conj : X →* MulAut X).ker.eq_bot_iff_forall.mpr
  intro x hx
  have hc (y : X) : y * x = x * y := by
    have he := DFunLike.congr_fun (show MulAut.conj x = 1 from hx) y
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  apply Prod.ext
  · exact NormalSymmetricThreePairRank.symmetricThree_center_trivial x.1
      (fun y => congrArg Prod.fst (hc (y,1)))
  · exact NormalSymmetricThreePairRank.symmetricThree_center_trivial x.2
      (fun y => congrArg Prod.snd (hc (1,y)))

/-- A subgroup of the automorphism group containing all inner automorphisms
is either the inner group or the whole group. -/
theorem inner_overgroup (R : Subgroup (MulAut X))
    (hR : (MulAut.conj : X →* MulAut X).range ≤ R) :
    R = (MulAut.conj : X →* MulAut X).range ∨ R = ⊤ := by
  by_cases hr : R ≤ (MulAut.conj : X →* MulAut X).range
  · exact Or.inl (le_antisymm hr hR)
  · right
    obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hr
    have hs : (MulEquiv.prodComm : MulAut X) ∈ R := by
      rcases inner_or_swap a with ⟨x,hx⟩ | ⟨x,hx⟩
      · exact (han ⟨x,hx.symm⟩).elim
      · have hh := R.mul_mem (R.inv_mem (hR ⟨x,rfl⟩)) ha
        rwa [hx,inv_mul_cancel_left] at hh
    apply top_unique
    intro b _
    rcases inner_or_swap b with ⟨x,rfl⟩ | ⟨x,rfl⟩
    · exact hR ⟨x,rfl⟩
    · exact R.mul_mem (hR ⟨x,rfl⟩) hs

noncomputable def pairFunction : X ≃* (Q → D) where
  toFun v i := if i = 1 then v.1 else v.2
  invFun v := (v 1, v (Multiplicative.ofAdd 1))
  left_inv v := by simp
  right_inv v := by
    funext i
    have hi : ∀ i : Q, i = 1 ∨ i = Multiplicative.ofAdd 1 := by decide
    rcases hi i with rfl | rfl <;> simp [show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 from by decide]
  map_mul' v w := by funext i; by_cases hi : i = 1 <;> simp [hi]

private theorem conj_injective : Function.Injective (MulAut.conj : D →* MulAut D) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (MulAut.conj : D →* MulAut D).ker.eq_bot_iff_forall.mpr
  intro x hx
  apply NormalSymmetricThreePairRank.symmetricThree_center_trivial
  intro y
  have he := DFunLike.congr_fun (show MulAut.conj x = 1 from hx) y
  change x * y * x⁻¹ = y at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

noncomputable def innerEquiv : D ≃* MulAut D :=
  MulEquiv.ofBijective MulAut.conj ⟨conj_injective,fun a => by
    obtain ⟨x,hx⟩ := NormalSymmetricThreePairRank.symmetricThree_aut_inner a
    exact ⟨x,hx.symm⟩⟩

noncomputable def wreathAut : W →* MulAut X := by
  letI := RegularWreathProduct.functionModule (MulAut D) Q D
  exact (MulAut.congr pairFunction).symm.toMonoidHom.comp
    ((MulDistribMulAction.toMulAut (RegularWreathProduct (MulAut D) Q) (Q → D)).comp
      (RegularWreathProduct.congr innerEquiv (MulEquiv.refl Q)).toMonoidHom)

private theorem wreathAut_pair (w : W) (v : X) (i : Q) :
    pairFunction (wreathAut w v) i =
      w.left i * pairFunction v (w.right⁻¹ * i) * (w.left i)⁻¹ := by
  letI := RegularWreathProduct.functionModule (MulAut D) Q D
  simp [wreathAut,MulAut.congr,RegularWreathProduct.functionModule_smul_apply,
    RegularWreathProduct.congr]
  rfl

private theorem wreathAut_injective : Function.Injective wreathAut := by
  intro w z h
  letI := RegularWreathProduct.functionModule (MulAut D) Q D
  letI : FaithfulSMul (RegularWreathProduct (MulAut D) Q) (Q → D) :=
    RegularWreathProduct.functionModule_faithful (MulAut D) Q D
  apply (RegularWreathProduct.congr innerEquiv (MulEquiv.refl Q)).injective
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Q → D)
  intro v
  obtain ⟨v,rfl⟩ := pairFunction.surjective v
  have hh := congrArg (fun a : MulAut X => pairFunction (a v)) h
  simpa [wreathAut,MulAut.congr] using hh

private theorem wreathAut_surjective : Function.Surjective wreathAut := by
  intro a
  rcases inner_or_swap a with ⟨x,hx⟩ | ⟨x,hx⟩
  · refine ⟨⟨pairFunction x,1⟩,?_⟩
    apply MulEquiv.ext
    intro v
    apply pairFunction.injective
    funext i
    rw [wreathAut_pair,hx]
    by_cases hi : i = 1 <;> simp [pairFunction,MulAut.conj_apply,hi]
  · refine ⟨⟨pairFunction x,Multiplicative.ofAdd 1⟩,?_⟩
    apply MulEquiv.ext
    intro v
    apply pairFunction.injective
    funext i
    rw [wreathAut_pair,hx]
    have hi : ∀i : Q, i = 1 ∨ i = Multiplicative.ofAdd 1 := by decide
    have ht : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
    have htinv : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide
    have htt : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases hi i with rfl | rfl <;>
      simp [pairFunction,MulAut.conj_apply,ht,htinv,htt]

/-- The literal automorphism group of S₃ × S₃ is its binary regular wreath product. -/
noncomputable def autEquiv : MulAut X ≃* W :=
  (MulEquiv.ofBijective wreathAut ⟨wreathAut_injective,wreathAut_surjective⟩).symm
end Theory.GroupTheory.SymmetricThreePairAutomorphisms


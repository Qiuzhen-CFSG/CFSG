module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.SpecificGroups.PSL5Two.TwoRankUpper
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank.Five
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.Alternating.Aut
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow

/-!
# Intrinsic binary linear automorphism two-ranks

This module exports the unconditional bounds `psl4_two_rank_le` and
`psl5_two_rank_le`, respectively four and six, for the full automorphism
groups of the concrete projective carriers.

The degree-four calculation uses the actual exceptional identification
`PSL₄(2) ≅ A₈` and the binary-tree Sylow model of `S₈`. The imported
degree-five calculation combines the inner-group bound with the fixed `S₆`
of an outer involution: an elementary subgroup meeting the graph coset has
inner kernel of rank at most four and total rank at most five. Transport
uses the genuine projective-to-linear equivalence. The inner six-dimensional
elementary subgroup also gives the re-exported equality `psl5_two_rank_eq`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3,
printed p.356 (PDF p.367).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace BinaryLinear.AutomorphismTwoRank

open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

private abbrev CTwo := Multiplicative (ZMod 2)
private abbrev D8 := DihedralGroup 4
private abbrev W8 := RegularWreathProduct D8 CTwo

private theorem ctwo_cases : ∀ c : CTwo, c = 1 ∨ c = Multiplicative.ofAdd 1 := by
  decide +revert

private def wreathBase : Subgroup W8 :=
  (RegularWreathProduct.rightHom : W8 →* CTwo).ker

private noncomputable def wreathBaseEquiv : wreathBase ≃* D8 × D8 where
  toFun x := (x.1.left 1, x.1.left (Multiplicative.ofAdd 1))
  invFun x := ⟨⟨fun c => if c = 1 then x.1 else x.2, 1⟩, by rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext c
      rcases ctwo_cases c with rfl | rfl <;> simp
    · change 1 = (x.1).right
      exact x.property.symm
  right_inv x := by simp
  map_mul' x y := by
    have hx : (x.1).right = 1 := x.property
    apply Prod.ext <;>
      change ((x.1 * y.1).left _) = _
    · simp [RegularWreathProduct.mul_left, hx]
    · simp [RegularWreathProduct.mul_left, hx]

private theorem wreathBase_rank : primeRank 2 wreathBase ≤ 4 := by
  rw [Theory.GroupTheory.primeRank_equiv 2 wreathBaseEquiv,
    primeRank_prod_eq_add]
  calc
    primeRank 2 D8 + primeRank 2 D8 ≤ 2 + 2 :=
      Nat.add_le_add (Theory.GroupTheory.dihedral_rank_le_two 2)
        (Theory.GroupTheory.dihedral_rank_le_two 2)
    _ = 4 := by norm_num

private theorem wreath_rank : primeRank 2 W8 ≤ 4 := by
  apply (primeRank_le_iff_elementary_card_le W8).mpr
  intro E hE
  let _ := hE
  let f : E →* CTwo :=
    (RegularWreathProduct.rightHom : W8 →* CTwo).comp E.subtype
  by_cases hEb : E ≤ wreathBase
  · have hi := Theory.GroupTheory.primeRank_le_of_injective 2
      (Subgroup.inclusion hEb) (Subgroup.inclusion_injective hEb)
    have hE' : primeRank 2 E ≤ primeRank 2 wreathBase := hi
    let e : E ≃* (E.subgroupOf wreathBase) := {
      toFun := fun x => ⟨⟨x, hEb x.property⟩, x.property⟩
      invFun := fun x => ⟨(x.1 : W8), x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intro x y; rfl }
    have hs := (primeRank_le_iff_elementary_card_le wreathBase).mp wreathBase_rank
      (E.subgroupOf wreathBase) (IsElementaryAbelian.subgroupOf hEb)
    rw [← Nat.card_congr e.toEquiv] at hs
    exact hs
  · obtain ⟨xE, hxE, hxB⟩ : ∃ x : W8, x ∈ E ∧ x ∉ wreathBase := by
      by_contra h
      apply hEb
      intro x hx
      by_contra hxb
      exact h ⟨x, hx, hxb⟩
    let x : W8 := xE
    have hx : x.right ≠ 1 := by
      intro hx1
      exact hxB (by
        change (x : W8).right = 1 at hx1
        exact hx1)
    have hxr : x.right = Multiplicative.ofAdd 1 := by
      rcases ctwo_cases x.right with h | h
      · exact (hx h).elim
      · exact h
    let ev : f.ker →* D8 := {
      toFun := fun y => (y.1 : W8).left 1
      map_one' := by rfl
      map_mul' := by
        intro y z
        have hy : (y.1 : W8).right = 1 := y.property
        have hz : (z.1 : W8).right = 1 := z.property
        change ((y.1 : W8) * (z.1 : W8)).left 1 = _
        simp [RegularWreathProduct.mul_left, hy]
    }
    have hev : Function.Injective ev := by
      intro y z hyz
      have hy1 : (y.1 : W8).right = 1 := y.property
      have hz1 : (z.1 : W8).right = 1 := z.property
      have hcy : (y.1 : W8) * x = x * (y.1 : W8) := by
        let xsub : E := ⟨x, hxE⟩
        have hh : (y.1 : E) * xsub = xsub * (y.1 : E) := mul_comm _ _
        simpa [xsub] using congrArg Subtype.val hh
      have hcz : (z.1 : W8) * x = x * (z.1 : W8) := by
        let xsub : E := ⟨x, hxE⟩
        have hh : (z.1 : E) * xsub = xsub * (z.1 : E) := mul_comm _ _
        simpa [xsub] using congrArg Subtype.val hh
      have hyc : (y.1 : W8).left (Multiplicative.ofAdd 1) =
          (x.left 1)⁻¹ * (y.1 : W8).left 1 * x.left 1 := by
        have hh := congrArg (fun w : W8 => w.left 1) hcy
        have hci : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide
        simp [RegularWreathProduct.mul_left, hxr, hy1, hci] at hh
        calc
          (y.1 : W8).left (Multiplicative.ofAdd 1) =
              (x.left 1)⁻¹ * (x.left 1 * (y.1 : W8).left (Multiplicative.ofAdd 1)) := by group
          _ = (x.left 1)⁻¹ * ((y.1 : W8).left 1 * x.left 1) := by rw [← hh]
          _ = (x.left 1)⁻¹ * (y.1 : W8).left 1 * x.left 1 := by group
      have hzc : (z.1 : W8).left (Multiplicative.ofAdd 1) =
          (x.left 1)⁻¹ * (z.1 : W8).left 1 * x.left 1 := by
        have hh := congrArg (fun w : W8 => w.left 1) hcz
        have hci : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide
        simp [RegularWreathProduct.mul_left, hxr, hz1, hci] at hh
        calc
          (z.1 : W8).left (Multiplicative.ofAdd 1) =
              (x.left 1)⁻¹ * (x.left 1 * (z.1 : W8).left (Multiplicative.ofAdd 1)) := by group
          _ = (x.left 1)⁻¹ * ((z.1 : W8).left 1 * x.left 1) := by rw [← hh]
          _ = (x.left 1)⁻¹ * (z.1 : W8).left 1 * x.left 1 := by group
      change (y.1 : W8).left 1 = (z.1 : W8).left 1 at hyz
      apply Subtype.ext
      apply Subtype.ext
      apply RegularWreathProduct.ext
      · funext c
        rcases ctwo_cases c with rfl | rfl
        · exact hyz
        · rw [hyc, hzc, hyz]
      · exact hy1.trans hz1.symm
    have hker : primeRank 2 f.ker ≤ 2 :=
      (Theory.GroupTheory.primeRank_le_of_injective 2 ev hev).trans
        (Theory.GroupTheory.dihedral_rank_le_two 2)
    have htarget : primeRank 2 CTwo ≤ 1 := by
      let P : Sylow 2 CTwo := Classical.choice inferInstance
      exact P.primeRank_le_one_of_isCyclic inferInstance
    have hr := Theory.GroupTheory.primeRank_le_ker_add (p := 2) f
    have hr' : primeRank 2 E ≤ 3 := hr.trans (by omega)
    have htop : IsElementaryAbelian 2 (⊤ : Subgroup E) := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        intro a
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 E) a.1 }
    have hcard := (primeRank_le_iff_elementary_card_le E).mp hr'
      (⊤ : Subgroup E) htop
    simpa using hcard.trans (by norm_num : 2 ^ 3 ≤ 2 ^ 4)

private theorem symmetric_eight_rank : primeRank 2 (Equiv.Perm (Fin 8)) ≤ 4 := by
  rw [Sylow.primeRank_eq treeSylow]
  rw [show (treeSylow : Subgroup (Equiv.Perm (Fin 8))) = treeGroup from treeSylow_coe]
  rw [Theory.GroupTheory.primeRank_equiv 2 treeWreathEquiv]
  exact wreath_rank

private theorem alternating_eight_automorphism_rank :
    primeRank 2 (MulAut (alternatingGroup (Fin 8))) ≤ 4 := by
  let a : Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      8 (by decide) (by decide))
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 a.symm.toMonoidHom a.symm.injective).trans
    symmetric_eight_rank

/-- The intrinsic two-rank bound for the binary degree-four automorphism group. -/
public theorem psl4_two_rank_le :
    primeRank 2 (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) ≤ 4 := by
  let e := Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)]
  exact alternating_eight_automorphism_rank

end BinaryLinear.AutomorphismTwoRank

end

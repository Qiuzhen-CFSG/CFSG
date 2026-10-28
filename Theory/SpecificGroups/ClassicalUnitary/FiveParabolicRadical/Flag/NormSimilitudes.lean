module
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.NormFiber
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# No A₆ section in a binary norm-similitude group over F₁₆

The norm multiplier is a genuine character. After removing this abelian
quotient, restriction to the norm-one pentagon is faithful because that fiber
spans the field. Its permutation group has order at most 120, excluding an
alternating-six section. The argument retains arbitrary section kernels.

Source application: Aschbacher--Smith 4.4.10--11, printed p.621,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.UnitaryFive.Flag
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H]

omit [Algebra (ZMod 2) F] in
private theorem fiber_card : Nat.card {x : F // x^5 = 1} ≤ 5 := by
  classical
  let j : {x : F // x^5 = 1} → {x // x ∈ (Polynomial.nthRoots 5 (1 : F)).toFinset} :=
    fun x => ⟨x.val,by simpa only [Multiset.mem_toFinset,
      Polynomial.mem_nthRoots (by decide : 0 < 5)] using x.property⟩
  have hi : Function.Injective j := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : {x // x ∈ (Polynomial.nthRoots 5 (1 : F)).toFinset} => z.val) he)
  have hh : Nat.card {x // x ∈ (Polynomial.nthRoots 5 (1 : F)).toFinset} ≤
      (Polynomial.nthRoots 5 (1 : F)).card := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
    exact Multiset.toFinset_card_le _
  exact (Nat.card_le_card_of_injective j hi).trans
    (hh.trans (Polynomial.card_nthRoots 5 (1 : F)))

/-- A faithful additive action by actual norm similitudes admits no A₆
section; the section map is not assumed to have a soluble kernel. -/
theorem no_six_section_of_norm_similitudes
    (hcard : Nat.card F = 16) (r : H →* MulAut (Multiplicative F))
    (hr : Function.Injective r)
    (hn : ∀ (a : H) (x : F), (r a (Multiplicative.ofAdd x)).toAdd ^ 5 =
      (r a (Multiplicative.ofAdd 1)).toAdd ^ 5 * x ^ 5)
    (U : Subgroup H) (q : U →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hns := Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
  have hne (a : H) : (r a (Multiplicative.ofAdd 1)).toAdd ≠ 0 := by
    intro he
    have hz : r a (Multiplicative.ofAdd 1) = 1 := congrArg Multiplicative.ofAdd he
    have heq := (r a).injective (hz.trans (map_one (r a)).symm)
    exact (one_ne_zero : (1 : F) ≠ 0) (congrArg Multiplicative.toAdd heq)
  let multiplier : H →* Fˣ := {
    toFun a := Units.mk0 ((r a (Multiplicative.ofAdd 1)).toAdd ^ 5) (pow_ne_zero _ (hne a))
    map_one' := by apply Units.ext; simp
    map_mul' a b := by
      apply Units.ext
      change (r (a*b) (Multiplicative.ofAdd 1)).toAdd ^ 5 =
        (r a (Multiplicative.ofAdd 1)).toAdd ^ 5 * (r b (Multiplicative.ofAdd 1)).toAdd ^ 5
      rw [map_mul]
      exact hn a (r b (Multiplicative.ofAdd 1)).toAdd }
  let : Group.IsSolvable (H ⧸ multiplier.ker) := Group.isSolvable_of_isSolvable_injective
    (f := (QuotientGroup.quotientKerEquivRange multiplier).toMonoidHom)
    (QuotientGroup.quotientKerEquivRange multiplier).injective
  obtain ⟨B,f,hf⟩ := simple_section_normal_of_solvable_quotient hns multiplier.ker U q hq
  have hnorm (a : multiplier.ker) (x : F) : (r a (Multiplicative.ofAdd x)).toAdd ^ 5 = x^5 := by
    have he : (r a.val (Multiplicative.ofAdd 1)).toAdd ^ 5 = 1 :=
      congrArg Units.val a.property
    rw [hn,he,one_mul]
  let X := {x : F // x^5 = 1}
  let a : multiplier.ker →* Equiv.Perm X := {
    toFun g := {
      toFun x := ⟨(r g.val (Multiplicative.ofAdd x.val)).toAdd,by rw [hnorm,x.property]⟩
      invFun x := ⟨(r (g⁻¹).val (Multiplicative.ofAdd x.val)).toAdd,by rw [hnorm,x.property]⟩
      left_inv x := by apply Subtype.ext; simp only [coe_inv,map_inv,ofAdd_toAdd,MulAut.inv_apply_self,toAdd_ofAdd]
      right_inv x := by apply Subtype.ext; simp only [coe_inv,map_inv,ofAdd_toAdd,MulAut.apply_inv_self,toAdd_ofAdd] }
    map_one' := by apply Equiv.ext; intro x; apply Subtype.ext; simp
    map_mul' g h := by
      apply Equiv.ext
      intro x
      apply Subtype.ext
      change (r (g.val*h.val) (Multiplicative.ofAdd x.val)).toAdd =
        (r g.val (r h.val (Multiplicative.ofAdd x.val))).toAdd
      rw [map_mul]
      rfl }
  have hai : Function.Injective a := by
    intro g h he
    apply Subtype.ext
    apply hr
    apply MulEquiv.ext
    intro x
    let lg : F →ₗ[ZMod 2] F := {
      (AddEquiv.toMultiplicative.symm (r g.val)).toAddMonoidHom with
      map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm (r g.val)) }
    let lh : F →ₗ[ZMod 2] F := {
      (AddEquiv.toMultiplicative.symm (r h.val)).toAddMonoidHom with
      map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm (r h.val)) }
    have hfiber : Set.EqOn lg lh {x : F | x^5 = 1} := by
      intro y hy
      exact congrArg Subtype.val (Equiv.congr_fun he (⟨y,hy⟩ : X))
    apply Multiplicative.toAdd.injective
    exact LinearMap.eqOn_span hfiber (by rw [normOne_span_eq_top hcard]; trivial)
  have hdiv := (card_dvd_of_surjective f hf).trans
    (card_dvd_of_injective (a.comp B.subtype) (hai.comp B.subtype_injective))
  rw [nat_card_alternatingGroup,Nat.card_perm] at hdiv
  have hd := hdiv.trans (Nat.factorial_dvd_factorial (fiber_card (F := F)))
  norm_num [Nat.factorial] at hd

end Theory.SpecificGroups.UnitaryFive.Flag

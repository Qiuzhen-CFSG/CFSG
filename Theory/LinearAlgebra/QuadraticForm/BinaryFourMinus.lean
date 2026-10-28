module
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Construction.Singular
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup.Transport
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Module.ZMod
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.GroupTheory.SolvableResidual

/-!
# Singular coordinates and perfect actors on a binary minus four-space

When singular vectors span and there is no totally singular plane, choose a
singular basis. Its distinct polar pairings all equal one. Matching that
basis with four of the five weight-four words identifies the whole quadratic
form with the five-point augmentation core. The existing faithful action on
its singular vectors embeds its isometry group in S5. A nontrivial perfect
subgroup therefore equals A5, since proper subgroups of A5 are solvable.

Only coordinate identities on 16 or 32 binary words use finite reduction.
The basis comparison and group argument retain the actual linear action.
Source application: Aschbacher--Smith G.10.15, p.363, and G.12.1(2), p.370.
-/

public noncomputable section
open Module BinaryPermutation
namespace QuadraticForm.BinaryFour
private abbrev Coord := Fin 4 → ZMod 2
private def word (x : Coord) : Full (Fin 5) :=
  ![x 1+x 2+x 3, x 0+x 2+x 3, x 0+x 1+x 3, x 0+x 1+x 2, x 0+x 1+x 2+x 3]
private theorem word_mem : ∀ x, word x ∈ core (Fin 5) := by
  change ∀ x : Coord, ∑ i, word x i = 0
  decide
private def coordinates : Coord ≃ₗ[ZMod 2] core (Fin 5) where
  toFun x := ⟨word x,word_mem x⟩
  invFun y := ![y.val 0+y.val 4,y.val 1+y.val 4,y.val 2+y.val 4,y.val 3+y.val 4]
  left_inv := by decide
  right_inv := by
    intro y
    apply Subtype.ext
    have h : ∀ w : Full (Fin 5), (∑ i, w i) = 0 →
        word ![w 0+w 4,w 1+w 4,w 2+w 4,w 3+w 4] = w := by decide
    exact h y.val y.property
  map_add' x y := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [word] <;> ring
  map_smul' a x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [word,mul_add]

private def model : QuadraticForm (ZMod 2) Coord :=
  FiveGeometry.form.comp coordinates.toLinearMap
private theorem model_basis : ∀ i : Fin 4, model (Pi.single i 1) = 0 := by decide
private theorem model_polar : ∀ i j : Fin 4,
    model.polarBilin (Pi.single i 1) (Pi.single j 1) = if i=j then 0 else 1 := by decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
private theorem quadratic_eq_of_basis {ι : Type*} (b : Basis ι (ZMod 2) V)
    (q r : QuadraticForm (ZMod 2) V)
    (hp : q.polarBilin = r.polarBilin) (hq : ∀ i, q (b i) = r (b i)) : q=r := by
  let f : V →+ ZMod 2 := {
    toFun x := q x-r x
    map_zero' := by simp
    map_add' := by
      intro x y
      rw [QuadraticMap.map_add q x y,QuadraticMap.map_add r x y]
      change q x+q y+q.polarBilin x y-(r x+r y+r.polarBilin x y)=_
      rw [hp]
      ring }
  let l : V →ₗ[ZMod 2] ZMod 2 := { f with map_smul' := ZMod.map_smul f }
  have hl : l=0 := b.ext (fun i => sub_eq_zero.mpr (hq i))
  apply QuadraticMap.ext
  intro x
  exact sub_eq_zero.mp (LinearMap.congr_fun hl x)

private theorem pair_dim (b : Basis (Fin 4) (ZMod 2) V) {i j : Fin 4} (hij : i≠j) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) {b i,b j})=2 := by
  have hi : Function.Injective (![i,j] : Fin 2 → Fin 4) := by
    intro a c hac
    fin_cases a <;> fin_cases c <;> simp_all
  have h := finrank_span_eq_card (b.linearIndependent.comp ![i,j] hi)
  have he : Set.range (b ∘ (![i,j] : Fin 2 → Fin 4)) = {b i,b j} := by
    ext x
    simp only [Set.mem_range,Function.comp_apply,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨k,rfl⟩
      fin_cases k <;> simp
    · rintro (rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  exact (congrArg (fun S : Set V => finrank (ZMod 2) (Submodule.span (ZMod 2) S)) he).symm.trans h

private theorem isometry_of_singular_basis (q : QuadraticForm (ZMod 2) V)
    (b : Basis (Fin 4) (ZMod 2) V) (hb : ∀ i, q (b i)=0)
    (hplane : ¬ ∃ U : Submodule (ZMod 2) V, finrank (ZMod 2) U=2 ∧ ∀ x∈U,q x=0) :
    Nonempty (q.IsometryEquiv FiveGeometry.form) := by
  classical
  have hpolar (i j : Fin 4) : q.polarBilin (b i) (b j)=if i=j then 0 else 1 := by
    by_cases hij : i=j
    · subst j
      simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
        show b i+b i=0 from (by simpa only [two_smul,zero_smul] using congrArg (fun c : ZMod 2 => c • b i) (show (2 : ZMod 2)=0 from by decide)),hb]
    · rw [if_neg hij]
      apply (show ∀ a : ZMod 2, a=0 ∨ a=1 from by decide) _ |>.resolve_left
      intro hz
      apply hplane
      refine ⟨Submodule.span (ZMod 2) {b i,b j},pair_dim b hij,?_⟩
      intro x hx
      obtain ⟨a,c,rfl⟩ := Submodule.mem_span_pair.mp hx
      rw [QuadraticMap.map_add q (a • b i) (c • b j),q.map_smul,q.map_smul,hb,hb]
      change _+_+q.polarBilin (a • b i) (c • b j)=0
      simp [hz]
  let r := model.comp b.equivFun.toLinearMap
  have he (i : Fin 4) : b.equivFun (b i)=Pi.single i 1 := by
    ext j
    simp [Basis.equivFun_self,Pi.single_apply,eq_comm]
  have hr : q=r := quadratic_eq_of_basis b q r (by
    apply LinearMap.ext_basis b b
    intro i j
    dsimp only [r]
    rw [QuadraticMap.polarBilin_comp]
    simp only [LinearMap.compl₁₂_apply,LinearEquiv.coe_coe]
    rw [he,he,model_polar,hpolar]) (by
      intro i
      change q (b i)=model (b.equivFun (b i))
      rw [he,model_basis,hb])
  exact ⟨{ toLinearEquiv := b.equivFun.trans coordinates
           map_app' := fun x => (congrArg (fun t : QuadraticForm (ZMod 2) V => t x) hr).symm }⟩


/-- A four-dimensional form with spanning singular vectors and no singular
plane has the literal five-point orthogonal coordinates. -/
theorem isometry_five_of_singular_span
    [FiniteDimensional (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)
    (hd : finrank (ZMod 2) V=4)
    (hspan : Submodule.span (ZMod 2) {x : V | q x=0}=⊤)
    (hplane : ¬ ∃ U : Submodule (ZMod 2) V, finrank (ZMod 2) U=2 ∧ ∀ x∈U,q x=0) :
    Nonempty (q.IsometryEquiv FiveGeometry.form) := by
  classical
  have hdim : finrank (ZMod 2) (Submodule.span (ZMod 2) {x : V | q x=0})=4 := by
    rw [hspan,finrank_top,hd]
  obtain ⟨f,hf,hfs,hfi⟩ := Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) {x : V | q x=0}
  let b' := Basis.mk hfi (hfs.trans hspan).ge
  let b := b'.reindex (finCongr hdim)
  have hb (i : Fin 4) : q (b i)=0 := by
    simpa only [b,b',Basis.reindex_apply,Basis.mk_apply,Set.mem_ofPred_eq] using hf ((finCongr hdim).symm i)
  exact isometry_of_singular_basis q b hb hplane


open Representation.OrthogonalFourMinus.FivePoint.Construction Subgroup
private def fivePermutation (g : FiveGeometry.form.isometrySubgroup) : Equiv.Perm (Fin 5) :=
  (exists_permutation_of_isometry g.val ((QuadraticMap.mem_isometrySubgroup _ _).mp g.property)).choose
private theorem fivePermutation_action (g : FiveGeometry.form.isometrySubgroup)
    (v : core (Fin 5)) : g.val v = coreRepresentation (Fin 5) (fivePermutation g) v :=
  (exists_permutation_of_isometry g.val ((QuadraticMap.mem_isometrySubgroup _ _).mp g.property)).choose_spec v
private def fiveHom : FiveGeometry.form.isometrySubgroup →* Equiv.Perm (Fin 5) where
  toFun := fivePermutation
  map_one' := by
    apply core_permutation_injective
    ext v
    rw [← fivePermutation_action]
    rfl
  map_mul' a b := by
    apply core_permutation_injective
    ext v
    rw [map_mul,Module.End.mul_apply,← fivePermutation_action,
      ← fivePermutation_action,← fivePermutation_action]
    rfl
private theorem fiveHom_injective : Function.Injective fiveHom := by
  intro a b hab
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [fivePermutation_action,fivePermutation_action]
  exact congrArg (fun p => coreRepresentation (Fin 5) p v) hab

private theorem perfect_five {A : Type*} [Group A] [Nontrivial A]
    [Group.IsPerfect A] (f : A →* Equiv.Perm (Fin 5)) (hf : Function.Injective f) :
    Nonempty (A ≃* alternatingGroup (Fin 5)) := by
  let sign := Equiv.Perm.sign.comp f
  let : Group.IsPerfect sign.range := Group.IsPerfect.range sign
  have he (a : A) : f a ∈ alternatingGroup (Fin 5) := by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    exact congrArg Subtype.val (Subsingleton.elim (sign.rangeRestrict a) 1)
  let j := f.codRestrict (alternatingGroup (Fin 5)) he
  have hj : Function.Injective j := fun _ _ h => hf (congrArg Subtype.val h)
  have ht : j.range = ⊤ := by
    by_contra hn
    let : Group.IsPerfect j.range := Group.IsPerfect.range j
    let : Group.IsSolvable j.range := alternatingGroup.isSolvable_subgroup_five_of_ne_top _ hn
    have hzero : (⊤ : Subgroup j.range) = ⊥ :=
      (solvableResidual_eq_top (G := j.range)).symm.trans solvableResidual_eq_bot
    obtain ⟨a,ha⟩ := exists_ne (1 : A)
    apply ha
    apply hj
    have hh := Subgroup.mem_bot.mp (hzero ▸ Subgroup.mem_top (j.rangeRestrict a))
    simpa using congrArg Subtype.val hh
  exact ⟨MulEquiv.ofBijective j ⟨hj,MonoidHom.range_eq_top.mp ht⟩⟩

/-- A nontrivial perfect group of isometries in minus-four coordinates is
A5, through the actual action on its five singular vectors. -/
theorem perfect_subgroup_equiv_alternatingFive
    [FiniteDimensional (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)
    (hd : finrank (ZMod 2) V=4)
    (hspan : Submodule.span (ZMod 2) {x : V | q x=0}=⊤)
    (hplane : ¬ ∃ U : Submodule (ZMod 2) V, finrank (ZMod 2) U=2 ∧ ∀ x∈U,q x=0)
    (K : Subgroup (V ≃ₗ[ZMod 2] V)) [Group.IsPerfect K]
    (hne : K ≠ ⊥) (hK : K ≤ q.isometrySubgroup) :
    Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := isometry_five_of_singular_span q hd hspan hplane
  let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  let f := fiveHom.comp (e.isometrySubgroupCongr.toMonoidHom.comp (Subgroup.inclusion hK))
  exact perfect_five f (fiveHom_injective.comp
    (e.isometrySubgroupCongr.injective.comp (Subgroup.inclusion_injective hK)))
end QuadraticForm.BinaryFour

module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.CommonActors
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Mathlib.LinearAlgebra.Projection

/-!
# Recombining the actual binary natural summands in B.5.1

A repeated natural prefix supplies one marking of the original actor. The
proved binary inner/graph theorem aligns the complementary natural module
with that marking or its dual. In the first case a linear concatenation gives
one more copy under the same actor.

For a mixed pair, two repeated coordinates would give an actual equivariant
quotient consisting of natural-plus-dual and one further natural module.
The same original quadratic offender has ratio at most one on this quotient.
B.4.9 forces its mixed pair to spend more than three quarters, and the given
intrinsic natural ratio forces the last factor to spend at least one quarter.
This contradiction leaves exactly one copy and gives the natural-plus-dual
alternative. The quarter bound and actual complement are the independent
source inputs; no marking-alignment or module-shape conclusion is assumed.

`binary_recombine_repeated` applies the marked construction to the literal
existential prefix produced by the source induction. Source: Aschbacher--Smith
B.5.1, printed pp.101--102, and B.4.9(2), printed pp.94--95.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
open scoped MatrixGroups BigOperators ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.BinaryRecombination
universe u v w z
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {X : Type w} [AddCommGroup X] [Module (ZMod 2) X]
  {Y : Type z} [AddCommGroup Y] [Module (ZMod 2) Y]

private def complementEquiv (ρ : Representation (ZMod 2) G V)
    (U W : Subrepresentation ρ) (hc : IsCompl U.toSubmodule W.toSubmodule) :
    ρ.Equiv (U.toRepresentation.prod W.toRepresentation) :=
  (Representation.Equiv.mk (U.toSubmodule.prodEquivOfIsCompl W.toSubmodule hc) (by
    intro g
    apply LinearMap.ext
    intro v
    change ρ g v.1.val + ρ g v.2.val = ρ g (v.1.val + v.2.val)
    exact (map_add _ _ _).symm)).symm

private def productEquiv {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G Z}
    {τ : Representation (ZMod 2) G X} {υ : Representation (ZMod 2) G Y}
    (e : ρ.Equiv τ) (f : σ.Equiv υ) : (ρ.prod σ).Equiv (τ.prod υ) :=
  .mk (e.toLinearEquiv.prodCongr f.toLinearEquiv) (by
    intro g
    apply LinearMap.ext
    intro v
    exact Prod.ext (LinearMap.congr_fun (e.isIntertwining' g) v.1)
      (LinearMap.congr_fun (f.isIntertwining' g) v.2))

private def repeatedSucc (π : Representation (ZMod 2) G X) (r : ℕ) :
    ((repeated π r).prod π).Equiv (repeated π (r+1)) :=
  .mk ((LinearEquiv.prodComm (ZMod 2) (Fin r → X) X).trans
    (Fin.consLinearEquiv (ZMod 2) (fun _ : Fin (r+1) => X))) (by
    intro g
    apply LinearMap.ext
    intro v
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl)

private def repeatedOne (π : Representation (ZMod 2) G X) : (repeated π 1).Equiv π where
  toFun v := v 0
  invFun x := fun _ => x
  left_inv v := by funext i; exact congrArg v (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl

private theorem ratio_le_action {H Z : Type*} [Group H]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H Z}
    (e : ActionEquiv ρ σ) (A : Subgroup G) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) : quadraticRatio σ ≤ actionRatio ρ A := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2
  have hAm : IsElementaryTwo (A.map e.groupEquiv.toMonoidHom) := by
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro hh
    apply hA.1
    apply Subgroup.map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
    simpa only [Subgroup.map_bot] using hh
  have hqm : IsQuadratic σ (A.map e.groupEquiv.toMonoidHom) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ w
    obtain ⟨v,rfl⟩ := e.linearEquiv.surjective w
    have hh := congrArg e.linearEquiv (hq a ha b hb v)
    change σ (e.groupEquiv a) (σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v) =
      σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v
    simpa only [e.intertwines,map_sub] using hh
  have hr : actionRatio σ (A.map e.groupEquiv.toMonoidHom) = actionRatio ρ A := by
    unfold actionRatio
    rw [← fixedCodim_map_equivariant ρ σ _ e.linearEquiv e.intertwines,
      rank_map_injective _ e.groupEquiv.injective]
  exact iInf_le_of_le (A.map e.groupEquiv.toMonoidHom) (iInf_le_of_le ⟨hAm,hqm⟩ hr.le)

private def pairProjection (r : ℕ) (hr : 0 < r) :
    (Fin r → X) × Y →ₗ[ZMod 2] X × Y where
  toFun v := (v.1 ⟨0,hr⟩,v.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem pairProjection_surjective (r : ℕ) (hr : 0 < r) :
    Function.Surjective (pairProjection (X := X) (Y := Y) r hr) :=
  fun v => ⟨(fun _ => v.1,v.2),rfl⟩

private def tripleProjection (r : ℕ) (hr : 2 ≤ r) :
    (Fin r → X) × Y →ₗ[ZMod 2] (X × Y) × X where
  toFun v := ((v.1 ⟨0,by omega⟩,v.2),v.1 ⟨1,by omega⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem tripleProjection_surjective (r : ℕ) (hr : 2 ≤ r) :
    Function.Surjective (tripleProjection (X := X) (Y := Y) r hr) := by
  classical
  rintro ⟨⟨x,y⟩,z⟩
  refine ⟨(fun i => if i.val = 0 then x else z,y), ?_⟩
  simp [tripleProjection]

private theorem mixed_repeated_not_ff [Finite G] [FiniteDimensional (ZMod 2) X]
    [FiniteDimensional (ZMod 2) Y] (π : Representation (ZMod 2) G X)
    (σ : Representation (ZMod 2) G Y) {d r : ℕ} (hd : d=4 ∨ d=5) (hr : 2 ≤ r)
    (hf : Function.Injective π) (a : ActionEquiv π (linearNatural BinaryField.two d))
    (e : σ.Equiv π.dual) (hlow : (1/4 : ℝ≥0∞) ≤ quadraticRatio (linearNatural BinaryField.two d))
    (hff : IsFFModule ((repeated π r).prod σ)) : False := by
  let ψ := (repeated π r).prod σ
  obtain ⟨A,hA⟩ := hff
  obtain ⟨B,_,hB,hq,_⟩ := hA.exists_quadratic_minimalBestOffender ψ
  have hsmall : fixedCodim ψ B ≤ rank B := (hB.1.isOffender ψ).2
  let p := pairProjection (X := X) (Y := Y) r (by omega)
  have hp : Function.Surjective p := pairProjection_surjective _ _
  have hpe : ∀ g v, p (ψ g v) = (π.prod σ) g (p v) := fun _ _ => rfl
  have hpair : IsFFModule (π.prod σ) := ⟨B,hB.1.1,
    (fixedCodim_le_of_equivariant_surjection ψ _ p hp hpe B).trans hsmall⟩
  have hgt := NaturalPair.three_quarters_lt_dual_ratio π σ hd hf a e hpair
  have hqp := quadratic_of_equivariant_surjection ψ _ p hp hpe B hq
  have hpairratio : (3/4 : ℝ≥0∞) < actionRatio (π.prod σ) B :=
    hgt.trans_le (iInf_le_of_le B (iInf_le_of_le ⟨hB.1.1,hqp⟩ le_rfl))
  have hπq := ((quadratic_prod_iff π σ B).mp hqp).1
  have hπratio : (1/4 : ℝ≥0∞) ≤ actionRatio π B :=
    hlow.trans (ratio_le_action a B hB.1.1 hπq)
  let t := tripleProjection (X := X) (Y := Y) r hr
  have ht : Function.Surjective t := tripleProjection_surjective _ _
  have hte : ∀ g v, t (ψ g v) = ((π.prod σ).prod π) g (t v) := fun _ _ => rfl
  have htcode := (fixedCodim_le_of_equivariant_surjection ψ _ t ht hte B).trans hsmall
  have hsum : actionRatio (π.prod σ) B + actionRatio π B ≤ 1 := by
    have hh := (actionRatio_le_one_iff ((π.prod σ).prod π) hB.1.1).mpr htcode
    simpa only [actionRatio,fixedCodim_prod,Nat.cast_add,ENNReal.add_div] using hh
  have hstrict := ENNReal.add_lt_add_of_lt_of_le (by norm_num : (1/4 : ℝ≥0∞) ≠ ⊤)
    hpairratio hπratio
  have heq : (3/4 : ℝ≥0∞) + 1/4 = 1 := by
    rw [← ENNReal.add_div]
    norm_num only [Nat.reduceAdd]
    exact ENNReal.div_self (by norm_num) (by norm_num)
  rw [heq] at hstrict
  exact (not_lt_of_ge hsum) hstrict


/-- Recombination keeps the original complementary subspaces and actor. -/
theorem binary_recombine_natural [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hff : IsFFModule ρ)
    (U W : Subrepresentation ρ) (hc : IsCompl U.toSubmodule W.toSubmodule)
    {d r : ℕ} (hd : d = 4 ∨ d = 5) (hr : 0 < r)
    (a : ActionEquiv U.toRepresentation (repeated (linearNatural BinaryField.two d) r))
    (hW : IsLinearNatural W.toRepresentation BinaryField.two d)
    (hlow : (1/4 : ℝ≥0∞) ≤ quadraticRatio (linearNatural BinaryField.two d)) :
    IsRepeatedLinearNatural ρ BinaryField.two d (r+1) ∨ (r=1 ∧ IsNaturalPlusDual ρ d) := by
  let π := (linearNatural BinaryField.two d).comp a.groupEquiv.toMonoidHom
  let eU : U.toRepresentation.Equiv (repeated π r) :=
    .mk a.linearEquiv (by
      intro g
      apply LinearMap.ext
      intro v
      exact a.intertwines g v)
  let mark : ActionEquiv π (linearNatural BinaryField.two d) :=
    ⟨a.groupEquiv,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  have hπ : Function.Injective π := by
    intro g h he
    apply a.groupEquiv.injective
    exact specialLinearNatural_injective d he
  rcases binary_naturals_same_or_dual W.toRepresentation π hd hW ⟨mark⟩ with hsame | hdual
  · obtain ⟨eW⟩ := hsame
    let e := (complementEquiv ρ U W hc).trans ((productEquiv eU eW).trans (repeatedSucc π r))
    refine Or.inl ⟨⟨a.groupEquiv, e.toLinearEquiv, ?_⟩⟩
    intro g v
    exact LinearMap.congr_fun (e.isIntertwining' g) v
  · obtain ⟨eW⟩ := hdual
    have hr1 : r = 1 := by
      by_contra hn
      have hr2 : 2 ≤ r := by omega
      let e := (complementEquiv ρ U W hc).trans (productEquiv eU (Representation.Equiv.refl _))
      have he : ∀ g v, e.toLinearEquiv (ρ g v) =
          ((repeated π r).prod W.toRepresentation) g (e.toLinearEquiv v) :=
        fun g v => LinearMap.congr_fun (e.isIntertwining' g) v
      have hf : IsFFModule ((repeated π r).prod W.toRepresentation) :=
        hff.map_equivariant ρ _ (MonoidHom.id G) Function.injective_id e.toLinearEquiv he
      exact mixed_repeated_not_ff π W.toRepresentation hd hr2 hπ mark eW hlow hf
    refine Or.inr ⟨hr1, ?_⟩
    subst r
    let e := (complementEquiv ρ U W hc).trans
      (productEquiv (eU.trans (repeatedOne π)) eW)
    refine ⟨⟨a.groupEquiv, e.toLinearEquiv, ?_⟩⟩
    intro g v
    have he := LinearMap.congr_fun (e.isIntertwining' g) v
    refine he.trans ?_
    apply Prod.ext
    · rfl
    · apply LinearMap.ext
      intro x
      change (e v).2 ((linearNatural BinaryField.two d) (a.groupEquiv g⁻¹) x) =
        (e v).2 ((linearNatural BinaryField.two d) (a.groupEquiv g)⁻¹ x)
      rw [map_inv]

/-- The source induction may supply the repeated prefix existentially;
its actual marking is chosen and aligned inside the recombination proof. -/
theorem binary_recombine_repeated [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hff : IsFFModule ρ)
    (U W : Subrepresentation ρ) (hc : IsCompl U.toSubmodule W.toSubmodule)
    {d r : ℕ} (hd : d = 4 ∨ d = 5) (hr : 0 < r)
    (hU : IsRepeatedLinearNatural U.toRepresentation BinaryField.two d r)
    (hW : IsLinearNatural W.toRepresentation BinaryField.two d)
    (hlow : (1/4 : ℝ≥0∞) ≤ quadraticRatio (linearNatural BinaryField.two d)) :
    IsRepeatedLinearNatural ρ BinaryField.two d (r+1) ∨ (r=1 ∧ IsNaturalPlusDual ρ d) := by
  obtain ⟨a⟩ := hU
  exact binary_recombine_natural ρ hff U W hc hd hr a hW hlow

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.BinaryRecombination

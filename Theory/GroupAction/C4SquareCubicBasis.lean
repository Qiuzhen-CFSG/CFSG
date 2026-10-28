module
public import Theory.GroupAction.C4SquareActionDichotomySetup
/-!
# Cubic actions on a homocyclic four-square

A nonidentity automorphism of cube one on C₄ × C₄ has no nontrivial
fixed point. Coordinates reduce the assertion to its two columns, without
enumerating the automorphism type. This supplies the fixed-point calculation
for splitting the abelian-core vertex in F.1.12(I)(8).

Source: Aschbacher–Smith F.1.12, printed pp.262–264; the finite calculation
uses the literal homocyclic coordinate model.
-/
public section
open scoped IsMulCommutative
namespace C4SquareExtension.Cubic
abbrev V := Model
private def e₁ : V := (Multiplicative.ofAdd 1,1)
private def e₂ : V := (1,Multiplicative.ofAdd 1)
private def act (p : V × V) (x : V) : V :=
  (Multiplicative.ofAdd (p.1.1.toAdd*x.1.toAdd+p.2.1.toAdd*x.2.toAdd),
   Multiplicative.ofAdd (p.1.2.toAdd*x.1.toAdd+p.2.2.toAdd*x.2.toAdd))
private def hom (p : V × V) : V →* V where
  toFun := act p
  map_one' := by simp [act]
  map_mul' x y := by ext <;> simp [act] <;> ring
private theorem columns (f : V →* V) (x : V) : f x = act (f e₁,f e₂) x := by
  have hd : x=e₁^x.1.toAdd.val*e₂^x.2.toAdd.val := by revert x; decide
  conv_lhs => rw [hd,map_mul,map_pow,map_pow]
  ext <;> simp [act, nsmul_eq_mul,mul_comm]
private def Cubic (p : V×V) : Prop :=
  act p (act p p.1)=e₁ ∧ act p (act p p.2)=e₂ ∧ p≠(e₁,e₂)
private instance (p : V×V) : Decidable (Cubic p) := by unfold Cubic; infer_instance
set_option maxRecDepth 4096 in
private theorem certificate : ∀ p : V×V, Cubic p →
    (∀ x,act p x=x → x=1) ∧
    ActionDichotomy.GoodBasis e₁ (act p e₁) := by decide +kernel

private def Inverts (p q : V×V) : Prop :=
  act q q.1=e₁ ∧ act q q.2=e₂ ∧
  act q (act p q.1)=act p p.1 ∧ act q (act p q.2)=act p p.2
private instance (p q : V×V) : Decidable (Inverts p q) := by unfold Inverts;infer_instance
set_option maxRecDepth 4096 in
private theorem swap_certificate : ∀ p : V×V, Cubic p → ∀q : V×V, Inverts p q →
    ∃x : V, ActionDichotomy.GoodBasis x (act p x) ∧ act q x=act p x := by decide +kernel

theorem fixed_free (a : MulAut V) (ha:a^3=1) (hne:a≠1) :
    ∀ x, a x=x → x=1 := by
  have he (x:V) : a x=act (a e₁,a e₂) x := columns a.toMonoidHom x
  have hp : Cubic (a e₁,a e₂) := by
    refine ⟨?_,?_,?_⟩
    · have h := DFunLike.congr_fun ha e₁
      simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply,
        ←he] using h
    · have h := DFunLike.congr_fun ha e₂
      simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply,
        ←he] using h
    · intro hh
      apply hne
      apply MulEquiv.ext
      intro x
      rw [he,hh]
      simp [act,e₁,e₂]
  intro x hx
  exact (certificate _ hp).1 x ((columns a.toMonoidHom x).symm.trans hx)
/-- An inverting involution swaps a basis of the homocyclic square. -/
theorem exists_swap_basis (a b : MulAut V) (ha : a^3=1) (hne : a≠1)
    (hb : b^2=1) (hba : ∀x, b (a (b x))=a (a x)) :
    ∃x : V, ActionDichotomy.GoodBasis x (a x) ∧ b x=a x ∧
      Subgroup.closure ({x,a x} : Set V)=⊤ := by
  have he (x:V) : a x=act (a e₁,a e₂) x := columns a.toMonoidHom x
  have hf (x:V) : b x=act (b e₁,b e₂) x := columns b.toMonoidHom x
  have hp : Cubic (a e₁,a e₂) := by
    refine ⟨?_,?_,?_⟩
    · have h := DFunLike.congr_fun ha e₁
      simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply,←he] using h
    · have h := DFunLike.congr_fun ha e₂
      simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply,←he] using h
    · intro hh
      apply hne
      apply MulEquiv.ext
      intro x
      rw [he,hh]
      simp [act,e₁,e₂]
  have hq : Inverts (a e₁,a e₂) (b e₁,b e₂) := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply,←hf] using
        DFunLike.congr_fun hb e₁
    · simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply,←hf] using
        DFunLike.congr_fun hb e₂
    · simpa only [←he,←hf] using hba e₁
    · simpa only [←he,←hf] using hba e₂
  obtain ⟨x,hx,hb⟩ := swap_certificate _ hp _ hq
  rw [←he] at hx
  rw [←he,←hf] at hb
  exact ⟨x,hx,hb,ActionDichotomy.goodBasis_base hx⟩

private noncomputable def basisAut (u v : V) (h : ActionDichotomy.GoodBasis u v) : MulAut V := by
  have hs : Function.Surjective (hom (u,v)) := by
    intro y
    obtain ⟨i,j,rfl⟩ := ActionDichotomy.goodBasis_decomp u v h y
    refine ⟨e₁^i.val*e₂^j.val,?_⟩
    rw [map_mul,map_pow,map_pow]
    simp [hom,act,e₁,e₂]
  exact MulEquiv.ofBijective (hom (u,v)) ⟨(Finite.injective_iff_surjective).mpr hs,hs⟩
private theorem basisAut_first (u v : V) (h : ActionDichotomy.GoodBasis u v) :
    basisAut u v h e₁=u := by simp [basisAut,hom,act,e₁]
private theorem basisAut_second (u v : V) (h : ActionDichotomy.GoodBasis u v) :
    basisAut u v h e₂=v := by simp [basisAut,hom,act,e₂]

/-- A marked change of basis in the literal homocyclic square. -/
theorem exists_equiv_of_good_bases (u v u' v' : V)
    (h : ActionDichotomy.GoodBasis u v) (h' : ActionDichotomy.GoodBasis u' v') :
    ∃ f : MulAut V, f u=u' ∧ f v=v' := by
  refine ⟨(basisAut u v h).symm.trans (basisAut u' v' h'),?_,?_⟩
  · change basisAut u' v' h' ((basisAut u v h).symm u)=u'
    have hh := congrArg (basisAut u v h).symm (basisAut_first u v h)
    rw [MulEquiv.symm_apply_apply] at hh
    rw [←hh,basisAut_first]
  · change basisAut u' v' h' ((basisAut u v h).symm v)=v'
    have hh := congrArg (basisAut u v h).symm (basisAut_second u v h)
    rw [MulEquiv.symm_apply_apply] at hh
    rw [←hh,basisAut_second]

theorem fixed_free_of_model {Q : Type*} [Group Q]
    (e : Q ≃* V) (a : MulAut Q) (ha : a^3=1) (hne : a≠1) :
    ∀ x, a x=x → x=1 := by
  let b := MulAut.congr e a
  have hb : b^3=1 := by rw [←map_pow,ha,map_one]
  have hn : b≠1 := fun h => hne ((MulAut.congr e).injective (h.trans (map_one _).symm))
  intro x hx
  apply e.injective
  rw [map_one]
  apply fixed_free b hb hn
  simpa only [b,MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using congrArg e hx
end C4SquareExtension.Cubic

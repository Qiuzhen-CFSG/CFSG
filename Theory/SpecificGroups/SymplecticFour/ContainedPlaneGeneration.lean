module
public import Theory.SpecificGroups.SymplecticFour.SmallPlaneGeneration
public import Theory.SpecificGroups.SymplecticFour.LargePlaneGeneration
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Theory.GroupAction.NormalizerConjugacyFibers
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Simultaneous selectors for large additive plane actors

Let P be a symplectic plane radical over a finite field of characteristic
two and order q > 2. Any additive subgroup A of P with order at least q²
has a plane-preserving conjugate whose join with A is P. No F-linear
closure or full root inside A is assumed.

In symmetric-matrix coordinates the binary trace annihilator of A has
at most q elements. Every nonzero dual orbit under the explicit Levi
transformations has more than (q-1)² elements. Counting transporter fibers
therefore gives a conjugate annihilator disjoint outside zero, proving
the plane-filling assertion. A fixed invertible upper shear adjusts the
same conjugator so its pair of opposite radicals generates Sp₄. Together
with a smaller plane actor J of order greater than q, this proves the
three-subgroup generation needed by the literal smaller-J source branch.

Source: the generation clauses of MS93 (5.6)(b--c), printed pp.917--918.
The actual full-kernel consumer is
NonbinarySymplectic.CriticalReduction.ContainedSelection; its selected
backward-path application is in SmallerLargePaths.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.ContainedPlane
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
private abbrev V (F : Type*) := F × F × F
private def dot (a v : V F) : F := a.1*v.1+a.2.1*v.2.1+a.2.2*v.2.2
private def shear (v : V F) : Sp F := (element 0 v.1 v.2.1 v.2.2).val
private def blockDiagonal : Subgroup (Sp F) :=
  planeParabolic ⊓ planeParabolic.comap
    (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom
omit [Finite F] in
private theorem mem_blockDiagonal (g : Sp F)
    (hlo : ∀ i j, g.val (Sum.inr i) (Sum.inl j)=0)
    (hup : ∀ i j, g.val (Sum.inl i) (Sum.inr j)=0) : g∈blockDiagonal := by
  refine ⟨(mem_planeParabolic_iff g).mpr hlo,?_⟩
  apply (mem_planeParabolic_iff _).mpr
  intro i j
  change ((TwoConjugate.opposition (F := F)).val * g.val *
    ((TwoConjugate.opposition (F := F))⁻¹).val) (Sum.inr i) (Sum.inl j)=0
  rw [TwoConjugate.opposition_inv]
  fin_cases i <;> fin_cases j <;>
    simp [TwoConjugate.opposition,Matrix.mul_apply,Fintype.sum_sum_type,
      Fin.sum_univ_two,Matrix.fromBlocks,Matrix.one_apply,hup]

private def compatible : Subgroup (V F ≃ₗ[F] V F) where
  carrier := {f | ∃ (e : V F ≃ₗ[F] V F) (g : Sp F),
    g∈blockDiagonal ∧ (∀ a v, dot (f a) v = dot a (e v)) ∧
    ∀ v, g * shear v * g⁻¹ = shear (e v)}
  one_mem' := ⟨1,1,blockDiagonal.one_mem,by intros; rfl,by intro v; simp⟩
  mul_mem' := by
    rintro f₁ f₂ ⟨e₁,g₁,b₁,h₁,k₁⟩ ⟨e₂,g₂,b₂,h₂,k₂⟩
    refine ⟨e₂*e₁,g₂*g₁,blockDiagonal.mul_mem b₂ b₁,?_,?_⟩
    · intro a v
      change dot (f₁ (f₂ a)) v = dot a (e₂ (e₁ v))
      rw [h₁,h₂]
    · intro v
      change (g₂*g₁)*shear v*(g₂*g₁)⁻¹ = shear (e₂ (e₁ v))
      rw [←k₂,←k₁]
      group
  inv_mem' := by
    rintro f ⟨e,g,b,h,k⟩
    refine ⟨e⁻¹,g⁻¹,blockDiagonal.inv_mem b,?_,?_⟩
    · intro a v
      have hh := h (f⁻¹ a) (e⁻¹ v)
      simpa using hh.symm
    · intro v
      have hh := k (e⁻¹ v)
      change g⁻¹*shear v*(g⁻¹)⁻¹ = shear (e⁻¹ v)
      rw [show shear v=g*shear (e⁻¹ v)*g⁻¹ by simpa using hh.symm]
      group
private def upper (t : F) : V F ≃ₗ[F] V F where
  toFun a := (a.1,a.2.1,a.2.2+a.1*t^2+a.2.1*t)
  invFun a := (a.1,a.2.1,a.2.2+a.1*t^2+a.2.1*t)
  left_inv a := by ext <;> simp [add_assoc,add_left_comm,add_comm,CharTwo.add_self_eq_zero]
  right_inv a := by ext <;> simp [add_assoc,add_left_comm,add_comm,CharTwo.add_self_eq_zero]
  map_add' a b := by ext <;> simp <;> ring
  map_smul' r a := by ext <;> simp <;> ring
private def lower (t : F) : V F ≃ₗ[F] V F where
  toFun a := (a.1+a.2.2*t^2+a.2.1*t,a.2.1,a.2.2)
  invFun a := (a.1+a.2.2*t^2+a.2.1*t,a.2.1,a.2.2)
  left_inv a := by ext <;> simp [add_assoc,add_left_comm,add_comm,CharTwo.add_self_eq_zero]
  right_inv a := by ext <;> simp [add_assoc,add_left_comm,add_comm,CharTwo.add_self_eq_zero]
  map_add' a b := by ext <;> simp <;> ring
  map_smul' r a := by ext <;> simp <;> ring
private def dilation (r : Fˣ) : V F ≃ₗ[F] V F :=
  LinearEquiv.smulOfUnit (r^2)
private def swap : V F ≃ₗ[F] V F where
  toFun a := (a.2.2,a.2.1,a.1)
  invFun a := (a.2.2,a.2.1,a.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Finite F] in
private theorem upper_compatible (t : F) : upper t ∈ compatible (F := F) := by
  let e : V F ≃ₗ[F] V F := {
    toFun v := (v.1+t^2*v.2.2,v.2.1+t*v.2.2,v.2.2)
    invFun v := (v.1+t^2*v.2.2,v.2.1+t*v.2.2,v.2.2)
    left_inv v := by ext <;> simp [add_assoc,add_left_comm,add_comm,CharTwo.add_self_eq_zero]
    right_inv v := by ext <;> simp [add_assoc,add_left_comm,add_comm,CharTwo.add_self_eq_zero]
    map_add' v w := by ext <;> simp <;> ring
    map_smul' r v := by ext <;> simp <;> ring }
  refine ⟨e,rootElement 6 t,?_,?_,?_⟩
  · apply mem_blockDiagonal <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [rootElement,rootMatrix,Matrix.single,Matrix.fromBlocks]
  · intro a v; dsimp [dot,upper,e]; ring
  · intro v
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    change rootMatrix 6 t * (element 0 v.1 v.2.1 v.2.2).val.val =
      (element 0 (v.1+t^2*v.2.2) (v.2.1+t*v.2.2) v.2.2).val.val * rootMatrix 6 t
    rw [element_matrix,element_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
        Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero,pow_two]
    all_goals ring_nf; simp [CharTwo.two_eq_zero]

omit [Finite F] in
private theorem swap_compatible : swap ∈ compatible (F := F) := by
  refine ⟨swap,rootElement 6 1*rootElement 7 1*rootElement 6 1,?_,?_,?_⟩
  · apply mem_blockDiagonal <;> intro i j
    all_goals
      change (rootMatrix 6 (1:F)*rootMatrix 7 1*rootMatrix 6 1 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) _ _=0
      fin_cases i <;> fin_cases j <;>
        simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
          Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero]
  · intro a v; dsimp [dot,swap]; ring
  · intro v
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    change (rootMatrix 6 1*rootMatrix 7 1*rootMatrix 6 1) *
        (element 0 v.1 v.2.1 v.2.2).val.val =
      (element 0 v.2.2 v.2.1 v.1).val.val * (rootMatrix 6 1*rootMatrix 7 1*rootMatrix 6 1)
    rw [element_matrix,element_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
        Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem lower_compatible (t : F) : lower t ∈ compatible (F := F) := by
  have he : lower t = swap * upper t * swap := by ext a <;> rfl
  rw [he]
  exact compatible.mul_mem (compatible.mul_mem swap_compatible (upper_compatible t)) swap_compatible

private def scaleFirst (r : Fˣ) : Sp F :=
  (rootElement 0 (r:F) * rootElement 1 ((r⁻¹:Fˣ):F) * rootElement 0 (r:F)) *
    (rootElement 0 1 * rootElement 1 1 * rootElement 0 1)
omit [Finite F] in
private theorem scaleFirst_matrix (r : Fˣ) : (scaleFirst r).val =
    diagonal (Sum.elim ![(r:F),1] ![((r⁻¹:Fˣ):F),1]) := by
  change (rootMatrix 0 (r:F) * rootMatrix 1 ((r⁻¹:Fˣ):F) * rootMatrix 0 (r:F)) *
    (rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero,Matrix.diagonal]
private def scaleSecond (r : Fˣ) : Sp F :=
  (rootElement 2 (r:F) * rootElement 3 ((r⁻¹:Fˣ):F) * rootElement 2 (r:F)) *
    (rootElement 2 1 * rootElement 3 1 * rootElement 2 1)
omit [Finite F] in
private theorem scaleSecond_matrix (r : Fˣ) : (scaleSecond r).val =
    diagonal (Sum.elim ![1,(r:F)] ![1,((r⁻¹:Fˣ):F)]) := by
  change (rootMatrix 2 (r:F) * rootMatrix 3 ((r⁻¹:Fˣ):F) * rootMatrix 2 (r:F)) *
    (rootMatrix 2 1 * rootMatrix 3 1 * rootMatrix 2 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero,Matrix.diagonal]
private def scalarSp (r : Fˣ) : Sp F := scaleFirst r * scaleSecond r
omit [Finite F] in
private theorem scalarSp_matrix (r : Fˣ) : (scalarSp r).val =
    diagonal (Sum.elim ![(r:F),(r:F)] ![((r⁻¹:Fˣ):F),((r⁻¹:Fˣ):F)]) := by
  change (scaleFirst r).val * (scaleSecond r).val = _
  rw [scaleFirst_matrix,scaleSecond_matrix,Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  rcases i with i | i <;> fin_cases i <;> simp
omit [Finite F] in
private theorem dilation_compatible (r : Fˣ) : dilation r ∈ compatible (F := F) := by
  refine ⟨dilation r,scalarSp r,?_,?_,?_⟩
  · apply mem_blockDiagonal <;> intro i j <;> rw [scalarSp_matrix] <;>
      simp [Matrix.diagonal]
  · intro a v
    change (r:F)^2*a.1*v.1+(r:F)^2*a.2.1*v.2.1+(r:F)^2*a.2.2*v.2.2 =
      a.1*((r:F)^2*v.1)+a.2.1*((r:F)^2*v.2.1)+a.2.2*((r:F)^2*v.2.2)
    ring
  · intro v
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    change (scalarSp r).val * (element 0 v.1 v.2.1 v.2.2).val.val =
      (element 0 ((r:F)^2*v.1) ((r:F)^2*v.2.1) ((r:F)^2*v.2.2)).val.val * (scalarSp r).val
    rw [scalarSp_matrix,element_matrix,element_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.fromBlocks,pow_two,
        mul_assoc,mul_comm,mul_left_comm]
    all_goals field_simp


private theorem card_le_mul_of_fibers {D C : Type*} [Finite D] [Finite C]
    (f : D → C) (m : ℕ) (hm : ∀ c, Nat.card {x // f x=c} ≤ m) :
    Nat.card D ≤ Nat.card C*m := by
  classical
  let := Fintype.ofFinite C
  rw [←Nat.card_congr (Equiv.sigmaFiberEquiv f),Nat.card_sigma]
  calc
    _ ≤ ∑ _c : C, m := Finset.sum_le_sum (fun c _ => hm c)
    _ = _ := by simp [Nat.card_eq_fintype_card]

omit [Finite F] in
private theorem quadratic_fiber (a b c d : F) (hb : b≠0) :
    Nat.card {t : F // c+a*t^2+b*t=d} ≤ 2 := by
  classical
  by_cases hn : Nonempty {t : F // c+a*t^2+b*t=d}
  · obtain ⟨t⟩ := hn
    have halt (s : {t : F // c+a*t^2+b*t=d}) :
        s.val=t.val ∨ s.val=t.val+b/a := by
      have he : (s.val+t.val)*(a*(s.val+t.val)+b)=0 := by
        have hh := s.property.trans t.property.symm
        linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hh
      rcases mul_eq_zero.mp he with he | he
      · exact Or.inl (CharTwo.add_eq_zero.mp he)
      · have ha : a≠0 := by intro ha; simp [ha,hb] at he
        right
        have he' := CharTwo.add_eq_zero.mp he
        have hs : s.val+t.val=b/a := (eq_div_iff ha).mpr (by simpa [mul_comm] using he')
        calc
          s.val = t.val+(s.val+t.val) := by rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]
          _ = t.val+b/a := by rw [hs]
    let code : {t : F // c+a*t^2+b*t=d} → Bool := fun s => decide (s.val=t.val)
    have hi : Function.Injective code := by
      intro s r he
      have he' : (s.val=t.val) ↔ (r.val=t.val) := by simpa [code] using he
      apply Subtype.ext
      rcases halt s with hs | hs
      · exact hs.trans (he'.mp hs).symm
      · rcases halt r with hr | hr
        · exact (he'.mpr hr).trans hr.symm
        · exact hs.trans hr.symm
    simpa using Nat.card_le_card_of_injective code hi
  · have : IsEmpty {t : F // c+a*t^2+b*t=d} := not_nonempty_iff.mp hn
    simp

/-- Concrete Levi transformations have orbits large enough for the
transporter count, including dual vectors with zero middle coefficient. -/
private theorem orbit_large (hq : 2 < Nat.card F) (a : V F) (ha : a≠0) :
    (Nat.card F-1)^2 < Nat.card (MulAction.orbit (compatible (F := F)) a) := by
  classical
  let G := compatible (F := F)
  have orbit_mem (f : V F ≃ₗ[F] V F) (hf : f ∈ G) : f a ∈ MulAction.orbit G a :=
    ⟨⟨f,hf⟩,rfl⟩
  by_cases hb : a.2.1=0
  · have hac : a.1≠0 ∨ a.2.2≠0 := by
      by_contra! hh
      apply ha
      exact Prod.ext hh.1 (Prod.ext hb hh.2)
    obtain ⟨a₀,b₀,c₀,he,heq,ha₀,hb₀⟩ :
        ∃ (a₀ b₀ c₀ : F) (e : G), e • a=(a₀,b₀,c₀) ∧ a₀≠0 ∧ b₀=0 := by
      rcases hac with h | h
      · exact ⟨a.1,a.2.1,a.2.2,1,rfl,h,hb⟩
      · exact ⟨a.2.2,a.2.1,a.1,⟨swap,swap_compatible⟩,rfl,h,hb⟩
    subst b₀
    have hreach (u : F) (v : Fˣ) : (u,0,(v:F)) ∈ MulAction.orbit G a := by
      obtain ⟨t,ht⟩ := (frobeniusEquiv F 2).surjective (((v:F)+c₀)/a₀)
      change t^2=((v:F)+c₀)/a₀ at ht
      have hcv : c₀+a₀*t^2=(v:F) := by rw [ht,mul_div_cancel₀ _ ha₀,add_comm (v:F) c₀,←add_assoc,CharTwo.add_self_eq_zero,zero_add]
      obtain ⟨s,hs⟩ := (frobeniusEquiv F 2).surjective ((u+a₀)/(v:F))
      change s^2=(u+a₀)/(v:F) at hs
      have hav : a₀+(v:F)*s^2=u := by rw [hs,mul_div_cancel₀ _ v.ne_zero,add_comm u a₀,←add_assoc,CharTwo.add_self_eq_zero,zero_add]
      refine ⟨(⟨lower s,lower_compatible s⟩ : G)*(⟨upper t,upper_compatible t⟩ : G)*he,?_⟩
      change ((⟨lower s,lower_compatible s⟩ : G)*(⟨upper t,upper_compatible t⟩ : G)*he) • a = _
      rw [mul_smul,mul_smul,heq]
      change (a₀+(c₀+a₀*t^2+0*t)*s^2+0*s,0,c₀+a₀*t^2+0*t)=(u,0,(v:F))
      simp [hcv,hav]
    let inj : F × Fˣ → MulAction.orbit G a := fun p => ⟨(p.1,0,(p.2:F)),hreach p.1 p.2⟩
    have hi : Function.Injective inj := by
      intro x y he
      have he' := congrArg Subtype.val he
      exact Prod.ext (congrArg (fun z : V F => z.1) he') (Units.ext (congrArg (fun z : V F => z.2.2) he'))
    have hc := Nat.card_le_card_of_injective inj hi
    rw [Nat.card_prod,Nat.card_units] at hc
    nlinarith [Nat.sub_add_cancel (show 1≤Nat.card F by omega)]
  · let point (p : Fˣ × F × F) : V F := dilation p.1 (lower p.2.2 (upper p.2.1 a))
    have hp (p : Fˣ × F × F) : point p ∈ MulAction.orbit G a :=
      orbit_mem (dilation p.1 * lower p.2.2 * upper p.2.1)
        (G.mul_mem (G.mul_mem (dilation_compatible p.1) (lower_compatible p.2.2)) (upper_compatible p.2.1))
    let f : Fˣ × F × F → MulAction.orbit G a := fun p => ⟨point p,hp p⟩
    have hfb (p : Fˣ × F × F) : (point p).2.1=(p.1:F)^2*a.2.1 := rfl
    have hfu (p : Fˣ × F × F) : (point p).2.2=
        (p.1:F)^2*(a.2.2+a.1*p.2.1^2+a.2.1*p.2.1) := rfl
    have hfl (p : Fˣ × F × F) : (point p).1=
        (p.1:F)^2*(a.1+(a.2.2+a.1*p.2.1^2+a.2.1*p.2.1)*p.2.2^2+a.2.1*p.2.2) := rfl
    have hfiber (y : MulAction.orbit G a) : Nat.card {p // f p=y} ≤ 4 := by
      by_cases hn : Nonempty {p // f p=y}
      · obtain ⟨p⟩ := hn
        let r : Fˣ := p.val.1
        let v : F := a.2.2+a.1*p.val.2.1^2+a.2.1*p.val.2.1
        let u : F := a.1+v*p.val.2.2^2+a.2.1*p.val.2.2
        have hr (z : {p // f p=y}) : z.val.1=r := by
          have he := congrArg (fun y : MulAction.orbit G a => y.val.2.1) (z.property.trans p.property.symm)
          change (z.val.1:F)^2*a.2.1=(r:F)^2*a.2.1 at he
          apply Units.ext
          exact (frobeniusEquiv F 2).injective (mul_right_cancel₀ hb he)
        have hv (z : {p // f p=y}) : a.2.2+a.1*z.val.2.1^2+a.2.1*z.val.2.1=v := by
          have he := congrArg (fun y : MulAction.orbit G a => y.val.2.2) (z.property.trans p.property.symm)
          change (point z.val).2.2=(point p.val).2.2 at he
          rw [hfu,hfu,hr] at he
          exact mul_left_cancel₀ (pow_ne_zero _ r.ne_zero) he
        have hu (z : {p // f p=y}) : a.1+v*z.val.2.2^2+a.2.1*z.val.2.2=u := by
          have he := congrArg (fun y : MulAction.orbit G a => y.val.1) (z.property.trans p.property.symm)
          change (point z.val).1=(point p.val).1 at he
          rw [hfl,hfl,hr,hv] at he
          exact mul_left_cancel₀ (pow_ne_zero _ r.ne_zero) he
        let c : {p // f p=y} → {t : F // a.2.2+a.1*t^2+a.2.1*t=v} ×
            {s : F // a.1+v*s^2+a.2.1*s=u} := fun z => ⟨⟨z.val.2.1,hv z⟩,⟨z.val.2.2,hu z⟩⟩
        have hi : Function.Injective c := by
          intro z w he
          apply Subtype.ext
          exact Prod.ext ((hr z).trans (hr w).symm)
            (Prod.ext (congrArg (fun z => z.1.val) he) (congrArg (fun z => z.2.val) he))
        have hc := Nat.card_le_card_of_injective c hi
        rw [Nat.card_prod] at hc
        exact hc.trans (Nat.mul_le_mul (quadratic_fiber a.1 a.2.1 a.2.2 v hb)
          (quadratic_fiber v a.2.1 a.1 u hb))
      · have : IsEmpty {p // f p=y} := not_nonempty_iff.mp hn
        simp
    have hc := card_le_mul_of_fibers f 4 hfiber
    rw [Nat.card_prod,Nat.card_prod,Nat.card_units] at hc
    have hq' : Nat.card F=Nat.card F-1+1 := by omega
    have hs : 0 < (Nat.card F-2)^2 := sq_pos_of_pos (by omega)
    have hq2 : 4*(Nat.card F-1)<Nat.card F*Nat.card F := by
      nlinarith [Nat.sub_add_cancel (show 2≤Nat.card F by omega)]
    have hm := Nat.mul_lt_mul_of_pos_left hq2 (show 0<Nat.card F-1 by omega)
    change (Nat.card F-1)^2 < Nat.card (MulAction.orbit G a)
    nlinarith

/-- If every relevant orbit exceeds the number of ordered pairs in s,
some translate of s misses s. Count fibers using a maximal stabilizer. -/
private theorem exists_separating_element {G X : Type*} [Group G] [Finite G]
    [MulAction G X] [Finite X] (s : Set X)
    (hs : ∀ x ∈ s, Nat.card s ^ 2 < Nat.card (MulAction.orbit G x)) :
    ∃ g : G, ∀ x ∈ s, g • x ∉ s := by
  classical
  let := Fintype.ofFinite X
  let := Fintype.ofFinite s
  by_cases hn : s.Nonempty
  · obtain ⟨a,ha,hmax⟩ := s.toFinite.toFinset.exists_max_image
      (fun x => Nat.card (MulAction.stabilizer G x)) (by simpa using hn)
    have ha' : a∈s := by simpa using ha
    have hm (x : s) : Nat.card (MulAction.stabilizer G x.val) ≤
        Nat.card (MulAction.stabilizer G a) := hmax x.val (by simp [x.property])
    by_contra! hbad
    let D := Σ p : s × s, {g : G // g • p.1.val=p.2.val}
    let f : D → G := fun z => z.2.val
    have hf : Function.Surjective f := by
      intro g
      obtain ⟨x,hx,hgx⟩ := hbad g
      exact ⟨⟨(⟨x,hx⟩,⟨g • x,hgx⟩),⟨g,rfl⟩⟩,rfl⟩
    have hfc (p : s × s) : Nat.card {g : G // g • p.1.val=p.2.val} ≤
        Nat.card (MulAction.stabilizer G a) := by
      by_cases he : ∃ g : G, g • p.1.val=p.2.val
      · obtain ⟨g,hg⟩ := he
        rw [MulAction.card_smul_fiber_of_witness _ _ g hg]
        exact hm p.1
      · have : IsEmpty {g : G // g • p.1.val=p.2.val} := ⟨fun g => he ⟨g.val,g.property⟩⟩
        simp
    have hc : Nat.card G ≤ Nat.card s^2 * Nat.card (MulAction.stabilizer G a) := by
      apply (Nat.card_le_card_of_surjective f hf).trans
      change Nat.card (Σ p : s × s, {g : G // g • p.1.val=p.2.val}) ≤ _
      rw [Nat.card_sigma]
      calc
        _ ≤ ∑ _p : s × s, Nat.card (MulAction.stabilizer G a) :=
          Finset.sum_le_sum (fun p _ => hfc p)
        _ = _ := by simp [←Nat.card_eq_fintype_card,Nat.card_prod,pow_two]
    have ho : Nat.card (MulAction.orbit G a)*Nat.card (MulAction.stabilizer G a)=Nat.card G := by
      rw [←Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G a)
    have hp : 0 < Nat.card (MulAction.stabilizer G a) := Nat.card_pos
    nlinarith [hs a ha']
  · exact ⟨1,fun x hx => (hn ⟨x,hx⟩).elim⟩

variable [Algebra (ZMod 2) F]
private def traceDot : LinearMap.BilinForm (ZMod 2) (V F) where
  toFun a := {
    toFun v := Algebra.trace (ZMod 2) F (dot a v)
    map_add' v w := by
      have he : dot a (v+w)=dot a v+dot a w := by dsimp [dot]; ring
      rw [he,map_add]
    map_smul' r v := by
      have he : dot a (r • v)=r • dot a v := by dsimp [dot]; simp only [Algebra.smul_def]; ring
      rw [he,map_smul]
      rfl }
  map_add' a b := by
    apply LinearMap.ext
    intro v
    have he : dot (a+b) v=dot a v+dot b v := by dsimp [dot]; ring
    change Algebra.trace (ZMod 2) F (dot (a+b) v)=_
    rw [he,map_add]
    rfl
  map_smul' r a := by
    apply LinearMap.ext
    intro v
    have he : dot (r • a) v=r • dot a v := by dsimp [dot]; simp only [Algebra.smul_def]; ring
    change Algebra.trace (ZMod 2) F (dot (r • a) v)=_
    rw [he,map_smul]
    rfl
omit [CharP F 2] [Finite F] in
private theorem traceDot_symm (a v : V F) : traceDot a v=traceDot v a := by
  change Algebra.trace (ZMod 2) F (dot a v)=Algebra.trace (ZMod 2) F (dot v a)
  congr 1
  dsimp [dot]
  ring
omit [CharP F 2] in
private theorem traceDot_nondegenerate : (traceDot (F := F)).Nondegenerate := by
  have hleft (a : V F) (ha : ∀ v, traceDot a v=0) : a=0 := by
    have h0 : a.1=0 := (traceForm_nondegenerate (ZMod 2) F).1 a.1 (by
      intro t
      simpa [traceDot,dot,Algebra.traceForm_apply] using ha (t,0,0))
    have h1 : a.2.1=0 := (traceForm_nondegenerate (ZMod 2) F).1 a.2.1 (by
      intro t
      simpa [traceDot,dot,Algebra.traceForm_apply] using ha (0,t,0))
    have h2 : a.2.2=0 := (traceForm_nondegenerate (ZMod 2) F).1 a.2.2 (by
      intro t
      simpa [traceDot,dot,Algebra.traceForm_apply] using ha (0,0,t))
    exact Prod.ext h0 (Prod.ext h1 h2)
  exact ⟨hleft,fun a ha => hleft a (fun v => (traceDot_symm a v).trans (ha v))⟩
omit [CharP F 2] in
private theorem card_orthogonal (S : Submodule (ZMod 2) (V F)) :
    Nat.card S * Nat.card (traceDot.orthogonal S) = Nat.card F^3 := by
  have hd := (traceDot (F := F)).finrank_add_finrank_orthogonal' S
  rw [traceDot_nondegenerate.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hd
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := traceDot.orthogonal S),
    ←pow_add,hd,←Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V F)]
  simp only [V,Nat.card_prod]
  ring

private theorem exists_additive_plane_pair (hq : 2 < Nat.card F)
    (S : Submodule (ZMod 2) (V F)) (hc : Nat.card F^2 ≤ Nat.card S) :
    ∃ (e : V F ≃ₗ[F] V F) (g : Sp F),
      g∈blockDiagonal ∧ (∀ v, g*shear v*g⁻¹=shear (e v)) ∧
      S ⊔ S.map (e.restrictScalars (ZMod 2)).toLinearMap = ⊤ := by
  classical
  let W := (traceDot (F := F)).orthogonal S
  have hcW : Nat.card W ≤ Nat.card F := by
    have hh := card_orthogonal S
    change Nat.card S * Nat.card W = Nat.card F^3 at hh
    have hp : 0 < Nat.card F^2 := pow_pos Nat.card_pos _
    nlinarith [Nat.mul_le_mul_right (Nat.card W) hc]
  let s : Set (V F) := {a | a∈W ∧ a≠0}
  have hcs : Nat.card s ≤ Nat.card F-1 := by
    let e : s ≃ {a : W // a≠0} := {
      toFun a := ⟨⟨a.val,a.property.1⟩,fun he => a.property.2 (congrArg Subtype.val he)⟩
      invFun a := ⟨a.val.val,a.val.property,fun he => a.property (Subtype.ext he)⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    rw [Nat.card_congr e]
    let := Fintype.ofFinite W
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
      Fintype.card_unique]
    rw [←Nat.card_eq_fintype_card]
    omega
  have : Finite (V F ≃ₗ[F] V F) := Finite.of_injective
    (fun f : V F ≃ₗ[F] V F => (f : V F → V F)) DFunLike.coe_injective
  obtain ⟨f,hf⟩ := exists_separating_element (G := compatible (F := F)) s (by
    intro a ha
    exact (Nat.pow_le_pow_left hcs 2).trans_lt (orbit_large hq a ha.2))
  obtain ⟨e,g,hgB,hpair,hg⟩ := f.property
  refine ⟨e,g,hgB,hg,?_⟩
  let T := S ⊔ S.map (e.restrictScalars (ZMod 2)).toLinearMap
  have hz : (traceDot (F := F)).orthogonal T=⊥ := by
    apply bot_unique
    intro a ha
    change a=0
    by_contra hn
    have haW : a∈W := fun v hv => ha v ((show S ≤ T from le_sup_left) hv)
    apply hf a ⟨haW,hn⟩
    refine ⟨?_,?_⟩
    · intro v hv
      change traceDot v (f.val a)=0
      rw [traceDot_symm]
      change Algebra.trace (ZMod 2) F (dot (f.val a) v)=0
      rw [hpair]
      change traceDot a (e v)=0
      rw [traceDot_symm]
      exact ha (e v) ((show S.map (e.restrictScalars (ZMod 2)).toLinearMap ≤ T from le_sup_right)
        (Submodule.mem_map.mpr ⟨v,hv,rfl⟩))
    · exact fun he => hn (f.val.injective (he.trans (map_zero f.val).symm))
  have hd := (traceDot (F := F)).finrank_add_finrank_orthogonal' T
  rw [traceDot_nondegenerate.ker_eq_bot,inf_bot_eq,hz,finrank_bot,add_zero,add_zero] at hd
  exact Submodule.eq_top_of_finrank_eq hd

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem shear_add (v w : V F) : shear (v+w)=shear v*shear w := by
  change (element 0 (v+w).1 (v+w).2.1 (v+w).2.2).val =
    (element 0 v.1 v.2.1 v.2.2 * element 0 w.1 w.2.1 w.2.2).val
  rw [element_mul]
  simp
omit [CharP F 2] [Finite F] [Algebra (ZMod 2) F] in
private theorem shear_zero : shear (0 : V F)=1 := by
  simp [shear,element,RootSubgroup.element_zero]
omit [Finite F] [Algebra (ZMod 2) F] in
private theorem shear_injective : Function.Injective (shear (F := F)) := by
  intro v w he
  have hh := (element_eq_iff _ _ _ _ _ _ _ _).mp (Subtype.ext he)
  exact Prod.ext hh.2.1 (Prod.ext hh.2.2.1 hh.2.2.2)
private abbrev P : Subgroup (Sp F) := (wing true).map unipotent.subtype
omit [Algebra (ZMod 2) F] in
private theorem mem_P (x : Sp F) : x∈P ↔ ∃ v : V F, shear v=x := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
    have hb : b=0 := (element_mem_wing true _ _ _ _).mp hy
    subst b
    exact ⟨(u,w,v),rfl⟩
  · rintro ⟨v,rfl⟩
    exact mem_map_of_mem unipotent.subtype ((element_mem_wing true _ _ _ _).mpr rfl)
private def coordinates (A : Subgroup (Sp F)) : AddSubgroup (V F) where
  carrier := {v | shear v∈A}
  zero_mem' := by change shear 0∈A; rw [shear_zero]; exact A.one_mem
  add_mem' := by intro v w hv hw; change shear (v+w)∈A; rw [shear_add]; exact A.mul_mem hv hw
  neg_mem' := by
    intro v hv
    have hn : -v=v := by ext <;> simp [CharTwo.neg_eq]
    change shear (-v)∈A
    rw [hn]
    exact hv
omit [Algebra (ZMod 2) F] in
private theorem coordinates_card (A : Subgroup (Sp F)) (hA : A≤P) :
    Nat.card (coordinates A)=Nat.card A := by
  let f : coordinates A → A := fun v => ⟨shear v.val,v.property⟩
  apply Nat.card_congr (Equiv.ofBijective f ⟨?_,?_⟩)
  · intro v w he
    have he' : shear v.val=shear w.val := congrArg (fun y : A => y.val) he
    exact Subtype.ext (shear_injective he')
  · intro x
    obtain ⟨v,hv⟩ := (mem_P x.val).mp (hA x.property)
    exact ⟨⟨v,by change shear v∈A; rw [hv]; exact x.property⟩,Subtype.ext hv⟩

private theorem exists_plane_pair (hq : 2 < Nat.card F)
    (A : Subgroup (Sp F)) (hAP : A≤P) (hc : Nat.card F^2≤Nat.card A) :
    ∃ k : Sp F, k∈blockDiagonal ∧ A ⊔ A.map (MulAut.conj k).toMonoidHom=P := by
  let S := AddSubgroup.toZModSubmodule 2 (coordinates A)
  have hcS : Nat.card F^2≤Nat.card S := by
    change Nat.card F^2≤Nat.card (coordinates A)
    rwa [coordinates_card A hAP]
  obtain ⟨e,k,hkB,hk,he⟩ := exists_additive_plane_pair hq S hcS
  have hkP : P.map (MulAut.conj k).toMonoidHom=P := by
    apply eq_of_le_of_card_ge
    · rintro x ⟨y,hy,rfl⟩
      obtain ⟨v,rfl⟩ := (mem_P y).mp hy
      change k*shear v*k⁻¹∈P
      rw [hk]
      exact (mem_P _).mpr ⟨e v,rfl⟩
    · exact (card_map_of_injective (MulAut.conj k).injective).ge
  refine ⟨k,hkB,le_antisymm (sup_le hAP (hkP ▸ map_mono hAP)) ?_⟩
  let T := AddSubgroup.toZModSubmodule 2 (coordinates (A ⊔ A.map (MulAut.conj k).toMonoidHom))
  have hST : S ⊔ S.map (e.restrictScalars (ZMod 2)).toLinearMap ≤ T := by
    apply sup_le
    · intro v hv
      exact (show A≤A ⊔ A.map (MulAut.conj k).toMonoidHom from le_sup_left) hv
    · rintro _ ⟨v,hv,rfl⟩
      change shear (e v)∈A ⊔ A.map (MulAut.conj k).toMonoidHom
      rw [←hk]
      exact mem_sup_right (mem_map_of_mem _ hv)
  rw [he] at hST
  intro x hx
  obtain ⟨v,rfl⟩ := (mem_P x).mp hx
  exact hST (Submodule.mem_top : v∈(⊤ : Submodule (ZMod 2) (V F)))

omit [CharP F 2] [Finite F] [Algebra (ZMod 2) F] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]
omit [CharP F 2] [Finite F] [Algebra (ZMod 2) F] in
private theorem map_conj_top (g : Sp F) :
    (⊤ : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom=⊤ := by
  rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective]
omit [Finite F] [Algebra (ZMod 2) F] in
private theorem shear_centralizes (v w : V F) : shear v*shear w*(shear v)⁻¹=shear w := by
  rw [←shear_add,add_comm,shear_add,mul_inv_cancel_right]
omit [Algebra (ZMod 2) F] in
private theorem shear_conj_subgroup (A : Subgroup (Sp F)) (hAP : A≤P) (v : V F) :
    A.map (MulAut.conj (shear v)).toMonoidHom=A := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨w,rfl⟩ := (mem_P y).mp (hAP hy)
    change shear v*shear w*(shear v)⁻¹∈A
    rwa [shear_centralizes]
  · intro hx
    obtain ⟨w,rfl⟩ := (mem_P x).mp (hAP hx)
    exact ⟨shear w,hx,shear_centralizes v w⟩

private abbrev opposite : Subgroup (Sp F) :=
  P.map (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom
private def unitShear : Sp F := shear (1,0,1)
omit [Finite F] [Algebra (ZMod 2) F] in
private theorem unitShear_inv : (unitShear (F := F))⁻¹=unitShear := by
  apply inv_eq_of_mul_eq_one_left
  change shear (1,0,1)*shear (1,0,1)=1
  rw [←shear_add]
  have hv : ((1,0,1) : V F)+(1,0,1)=0 := by ext <;> simp [CharTwo.add_self_eq_zero]
  rw [hv,shear_zero]
omit [Finite F] [Algebra (ZMod 2) F] in
private theorem unitShear_matrix : (unitShear (F := F)).val=fromBlocks 1 1 0 1 := by
  change (element 0 (1:F) 0 1).val.val=_
  rw [element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks,Matrix.one_apply]
omit [Finite F] [Algebra (ZMod 2) F] in
private theorem shifted_opposition : unitShear *
    (TwoConjugate.opposition*unitShear*TwoConjugate.opposition⁻¹) * unitShear⁻¹ =
      TwoConjugate.opposition (F := F) := by
  rw [unitShear_inv,TwoConjugate.opposition_inv]
  apply Subtype.ext
  change (unitShear (F := F)).val *
    ((TwoConjugate.opposition (F := F)).val * (unitShear (F := F)).val *
      (TwoConjugate.opposition (F := F)).val) * (unitShear (F := F)).val = _
  rw [unitShear_matrix]
  have h11 : (1+1 : Matrix (Fin 2) (Fin 2) F)=0 := by
    ext i j
    simp [Matrix.one_apply,CharTwo.add_self_eq_zero]
  simp [TwoConjugate.opposition,Matrix.fromBlocks_multiply,h11]

private theorem shifted_planes_generate (hq : 2 < Nat.card F) :
    opposite ⊔ opposite.map (MulAut.conj (unitShear (F := F))⁻¹).toMonoidHom=⊤ := by
  let H := opposite ⊔ opposite.map (MulAut.conj (unitShear (F := F))⁻¹).toMonoidHom
  have ho : TwoConjugate.opposition (F := F)∈H := by
    have hp : unitShear (F := F)∈P := (mem_P _).mpr ⟨(1,0,1),rfl⟩
    have hl : TwoConjugate.opposition*unitShear*TwoConjugate.opposition⁻¹∈opposite :=
      mem_map_of_mem (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom hp
    have hh : unitShear*(TwoConjugate.opposition*unitShear*TwoConjugate.opposition⁻¹)*unitShear⁻¹∈
        opposite.map (MulAut.conj (unitShear (F := F))).toMonoidHom :=
      ⟨_,hl,rfl⟩
    rw [shifted_opposition] at hh
    apply (show opposite.map (MulAut.conj (unitShear (F := F))).toMonoidHom≤H from ?_) hh
    dsimp only [H]
    rw [unitShear_inv]
    exact le_sup_right
  have hP : P≤H := by
    intro y hy
    have hh := H.mul_mem (H.mul_mem ho
      (mem_sup_left (mem_map_of_mem (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom hy)))
      (H.inv_mem ho)
    change TwoConjugate.opposition*(TwoConjugate.opposition*y*TwoConjugate.opposition⁻¹)*
      TwoConjugate.opposition⁻¹∈H at hh
    have hoo : TwoConjugate.opposition (F := F)*TwoConjugate.opposition=1 := by
      nth_rw 1 [←TwoConjugate.opposition_inv]
      exact inv_mul_cancel _
    have he : TwoConjugate.opposition*(TwoConjugate.opposition*y*TwoConjugate.opposition⁻¹)*
        TwoConjugate.opposition⁻¹=y := by
      simp only [TwoConjugate.opposition_inv]
      calc
        _ = (TwoConjugate.opposition*TwoConjugate.opposition)*y*
            (TwoConjugate.opposition*TwoConjugate.opposition) := by group
        _ = y := by rw [hoo,one_mul,mul_one]
    rwa [he] at hh
  apply top_unique
  have ht := LargePlaneGeneration.opposite_plane_large_subactor_generate
    (P (F := F)) (by rw [SymplecticConjugatePair.planeRadical_eq_wing]) (by
      rw [card_map_of_injective unipotent.subtype_injective,card_wing]
      simpa only [pow_one] using Nat.pow_lt_pow_right
        (show 1<Nat.card F by omega) (by decide : 1<3))
  rw [SymplecticConjugatePair.planeRadical_eq_wing] at ht
  rw [←ht]
  exact sup_le le_sup_left hP

private theorem blockDiagonal_normalizes {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    {k : Sp F} (hk : k∈blockDiagonal) :
    P.map (MulAut.conj k).toMonoidHom=P ∧
    opposite.map (MulAut.conj k).toMonoidHom=opposite := by
  have hPN : normalizer (P (F := F) : Set (Sp F))=planeParabolic := by
    change normalizer (((wing true).map (unipotent (F := F)).subtype) : Set (Sp F))=_
    rw [←SymplecticConjugatePair.planeRadical_eq_wing]
    exact planeRadicalAmbient_normalizer hF hn
  constructor
  · exact mem_normalizer_iff_map_conj_eq.mp (hPN ▸ hk.1)
  · have hko : TwoConjugate.opposition*k*TwoConjugate.opposition⁻¹∈
        normalizer (P (F := F) : Set (Sp F)) := hPN ▸ hk.2
    have he := mem_normalizer_iff_map_conj_eq.mp hko
    change P.map (MulAut.conj (TwoConjugate.opposition*k*TwoConjugate.opposition⁻¹)).toMonoidHom=P at he
    apply Subgroup.map_injective (f := (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom)
      (MulAut.conj _).injective
    change ((P.map (MulAut.conj TwoConjugate.opposition).toMonoidHom).map
      (MulAut.conj k).toMonoidHom).map (MulAut.conj TwoConjugate.opposition).toMonoidHom =
      (P.map (MulAut.conj TwoConjugate.opposition).toMonoidHom).map
        (MulAut.conj TwoConjugate.opposition).toMonoidHom
    rw [map_conj_mul,map_conj_mul,map_conj_mul]
    rw [←TwoConjugate.opposition_inv] at he
    have hoo : TwoConjugate.opposition (F := F)*TwoConjugate.opposition=1 := by
      nth_rw 1 [←TwoConjugate.opposition_inv]
      exact inv_mul_cancel _
    rw [hoo]
    simpa only [TwoConjugate.opposition_inv,show
      (MulAut.conj (1 : Sp F)).toMonoidHom=MonoidHom.id _ by ext y; simp,
      Subgroup.map_id] using he

/-- Any plane actor of order at least q² has a plane-preserving second
conjugate filling the plane. The same element makes the two opposite
full radicals generate. No F-linear closure of the actor is assumed. -/
theorem exists_contained_plane_selector {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (A : Subgroup (Sp F)) (hAP : A≤((wing true).map (unipotent (F := F)).subtype)) (hc : Nat.card F^2≤Nat.card A) :
    ∃ x : Sp F,
      A ⊔ A.map (MulAut.conj x).toMonoidHom=((wing true).map (unipotent (F := F)).subtype) ∧
      (((wing true).map (unipotent (F := F)).subtype).map (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom) ⊔ (((wing true).map (unipotent (F := F)).subtype).map (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom=⊤ ∧
      x∈normalizer (((wing true).map (unipotent (F := F)).subtype) : Set (Sp F)) := by
  have hq : 2<Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) hn)
  obtain ⟨k,hk,hA⟩ := exists_plane_pair hq A hAP hc
  obtain ⟨hkP,hkO⟩ := blockDiagonal_normalizes hF hn hk
  let x := unitShear*k
  have hpP : P.map (MulAut.conj (unitShear (F := F))).toMonoidHom=P :=
    shear_conj_subgroup P le_rfl (1,0,1)
  refine ⟨x,?_,?_,?_⟩
  · change A ⊔ A.map (MulAut.conj (unitShear*k)).toMonoidHom=P
    rw [←map_conj_mul]
    change A ⊔ (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj (shear (1,0,1))).toMonoidHom=P
    rw [shear_conj_subgroup _ (hkP ▸ map_mono hAP) (1,0,1)]
    exact hA
  · apply Subgroup.map_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
    rw [Subgroup.map_sup,map_conj_top]
    change opposite.map (MulAut.conj k).toMonoidHom ⊔
      (opposite.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj k).toMonoidHom=⊤
    rw [hkO,map_conj_mul]
    rw [show k*x⁻¹=(unitShear (F := F))⁻¹ by dsimp [x]; group]
    exact shifted_planes_generate hq
  · apply mem_normalizer_iff_map_conj_eq.mpr
    change P.map (MulAut.conj (unitShear*k)).toMonoidHom=P
    rw [←map_conj_mul,hkP,hpP]

/-- The proper smaller plane mover and a large contained critical actor
admit a single simultaneous generation and full-plane selector. -/
theorem exists_smaller_contained_generators {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (J A : Subgroup (Sp F)) (hJP : J≤((wing true).map (unipotent (F := F)).subtype)) (hJc : Nat.card F<Nat.card J)
    (hAP : A≤((wing true).map (unipotent (F := F)).subtype)) (hAc : Nat.card F^2≤Nat.card A) :
    ∃ g x : Sp F,
      (J.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔ A.map (MulAut.conj x).toMonoidHom=⊤ ∧
      (((wing true).map (unipotent (F := F)).subtype).map (MulAut.conj g).toMonoidHom ⊔
        (((wing true).map (unipotent (F := F)).subtype).map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom=⊤) ∧
      x∈normalizer (((wing true).map (unipotent (F := F)).subtype) : Set (Sp F)) := by
  obtain ⟨x,hA,hpair,hpos⟩ := exists_contained_plane_selector hF hn A hAP hAc
  refine ⟨TwoConjugate.opposition,x,?_,hpair,hpos⟩
  rw [sup_assoc,hA]
  have hh := LargePlaneGeneration.opposite_plane_large_subactor_generate J
    (by rwa [SymplecticConjugatePair.planeRadical_eq_wing]) hJc
  have hh' := congrArg (Subgroup.map (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom) hh
  rw [Subgroup.map_sup,map_conj_mul,map_conj_top] at hh'
  have hoo : TwoConjugate.opposition (F := F)*TwoConjugate.opposition=1 := by
    nth_rw 1 [←TwoConjugate.opposition_inv]
    exact inv_mul_cancel _
  rw [hoo,show (MulAut.conj (1 : Sp F)).toMonoidHom=MonoidHom.id _ by ext y; simp,
    Subgroup.map_id,SymplecticConjugatePair.planeRadical_eq_wing,sup_comm] at hh'
  exact hh'

end Theory.SpecificGroups.SymplecticFour.ContainedPlane

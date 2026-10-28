module
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic
/-!
# Cubic Singer centralizers

A ternary matrix whose cube is a scalar with no cube root in the coefficient
field generates a cubic field. Evaluation at a nonzero vector identifies the
natural module with this field. Every commuting operator is multiplication by
a field element, and its determinant is the field norm. Thus the centralizer
in SL₃ is the cyclic norm kernel, of order q²+q+1.

This supplies the nonsplit linear centralizer calculation in Aschbacher–Smith,
A.3.18, printed p.53. The construction retains the supplied matrix itself.
-/

@[expose] public noncomputable section
open Polynomial Matrix
namespace Matrix.CubicSinger
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

def polynomial (z : F) : F[X] := X^3-C z

theorem irreducible_polynomial (z : F) (hn : ∀ a : F, a^3≠z) :
    Irreducible (polynomial z) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [polynomial]
  · intro a ha
    exact hn a (sub_eq_zero.mp (by simpa [polynomial,IsRoot] using ha))

theorem cubic_finrank (z : F) : Module.finrank F (AdjoinRoot (polynomial z))=3 := by
  have hp : (polynomial z).Monic := monic_X_pow_sub_C z (by decide)
  exact (AdjoinRoot.powerBasis hp.ne_zero).finrank.trans natDegree_X_pow_sub_C

def action (f : Module.End F V) (z : F) (hc : f^3 = algebraMap F _ z) :
    AdjoinRoot (polynomial z) →ₐ[F] Module.End F V := by
  apply Ideal.Quotient.liftₐ _ (aeval f)
  intro a ha
  obtain ⟨b,rfl⟩ := Ideal.mem_span_singleton.mp ha
  rw [map_mul]
  have h : aeval f (polynomial z)=0 := by simp [polynomial,hc]
  rw [h,zero_mul]

theorem action_root (f : Module.End F V) (z : F) (hc : f^3 = algebraMap F _ z) :
    action f z hc (AdjoinRoot.root (polynomial z)) = f := by
  change aeval f X = f
  exact aeval_X f

/-- Evaluation of a field of operators at a specified vector. -/
def evaluation {E : Type*} [CommRing E] [Algebra F E]
    (φ : E →ₐ[F] Module.End F V) (v : V) : E →ₗ[F] V where
  toFun a := φ a v
  map_add' a b := by simp
  map_smul' a b := by simp

private theorem evaluation_injective {E : Type*} [Field E] [Algebra F E]
    (φ : E →ₐ[F] Module.End F V) (v : V) (hv : v≠0) :
    Function.Injective (evaluation φ v) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_contra hn
  apply hv
  have h := congrArg (fun w => φ a⁻¹ w) ha
  change (φ a⁻¹ * φ a) v = _ at h
  rw [←map_mul,inv_mul_cancel₀ hn,map_one] at h
  simpa using h

variable [FiniteDimensional F V]

theorem action_evaluation_bijective (f : Module.End F V) (z : F)
    (hc : f^3 = algebraMap F _ z) (hn : ∀ a : F, a^3≠z)
    (hd : Module.finrank F V = 3) (v : V) (hv : v≠0) :
    Function.Bijective (evaluation (action f z hc) v) := by
  let : Fact (Irreducible (polynomial z)) := ⟨irreducible_polynomial z hn⟩
  have hdim : Module.finrank F (AdjoinRoot (polynomial z)) = Module.finrank F V := by
    exact (cubic_finrank z).trans hd.symm
  let : FiniteDimensional F (AdjoinRoot (polynomial z)) := Module.finite_of_finrank_pos (by omega)
  have hi := evaluation_injective (action f z hc) v hv
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

variable [Nontrivial V]

omit [FiniteDimensional F V] [Nontrivial V] in
theorem action_commute (f : Module.End F V) (z : F)
    (hc : f^3 = algebraMap F _ z) (g : Module.End F V) (hg : Commute f g)
    (b : AdjoinRoot (polynomial z)) : Commute (action f z hc b) g := by
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective b
  change Commute (aeval f p) g
  apply (Algebra.commute_of_mem_adjoin_singleton_of_commute (R := F) ?_ hg.symm).symm
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨p,rfl⟩

theorem action_centralizer (f : Module.End F V) (z : F)
    (hc : f^3 = algebraMap F _ z) (hn : ∀ a : F, a^3≠z)
    (hd : Module.finrank F V = 3) (g : Module.End F V) (hg : Commute f g) :
    ∃ b : AdjoinRoot (polynomial z), action f z hc b = g := by
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  have hbij := action_evaluation_bijective f z hc hn hd v hv
  obtain ⟨b,hb⟩ := hbij.surjective (g v)
  refine ⟨b,?_⟩
  ext w
  obtain ⟨c,rfl⟩ := hbij.surjective w
  change (action f z hc b * action f z hc c) v =
    (g * action f z hc c) v
  rw [←map_mul,mul_comm b c,map_mul]
  rw [←(action_commute f z hc g hg c).eq]
  change action f z hc c (action f z hc b v) = action f z hc c (g v)
  rw [show action f z hc b v = g v from hb]

theorem action_det (f : Module.End F V) (z : F)
    (hc : f^3 = algebraMap F _ z) (hn : ∀ a : F, a^3≠z)
    (hd : Module.finrank F V = 3) (b : AdjoinRoot (polynomial z)) :
    LinearMap.det (action f z hc b) = Algebra.norm F b := by
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  let e := LinearEquiv.ofBijective (evaluation (action f z hc) v)
    (action_evaluation_bijective f z hc hn hd v hv)
  have he : action f z hc b = e.toLinearMap ∘ₗ Algebra.lmul F _ b ∘ₗ e.symm.toLinearMap := by
    apply LinearMap.ext
    intro w
    obtain ⟨c,rfl⟩ := e.surjective w
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    change (action f z hc b * action f z hc c) v = action f z hc (b*c) v
    rw [map_mul]
  rw [he,LinearMap.det_conj]
  rfl

end Matrix.CubicSinger
namespace Matrix.CubicSinger
section Matrices
variable {F : Type*} [Field F]
open Subgroup
open scoped MatrixGroups
variable [Finite F]

/-- The exact centralizer in SL₃ of the supplied nonsplit scalar-cube matrix. -/
theorem matrix_centralizer (g : GL (Fin 3) F) (z : F)
    (hc : g.val^3 = Matrix.scalar (Fin 3) z) (hn : ∀ a : F, a^3≠z) :
    IsCyclic ((centralizer ({g} : Set (GL (Fin 3) F))).comap SpecialLinearGroup.toGL) ∧
    Nat.card ((centralizer ({g} : Set (GL (Fin 3) F))).comap SpecialLinearGroup.toGL) =
      Nat.card F^2+Nat.card F+1 := by
  classical
  let E := AdjoinRoot (polynomial z)
  let : Fact (Irreducible (polynomial z)) := ⟨irreducible_polynomial z hn⟩
  let : Field E := inferInstance
  have hdE : Module.finrank F E=3 := cubic_finrank z
  let : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let : Finite E := (Module.finite_iff_finite (R := F) (M := E)).mp inferInstance
  let f := Matrix.toLin' g.val
  have hf : f^3=algebraMap F _ z := by
    change (Matrix.toLinAlgEquiv' g.val)^3 = _
    rw [←map_pow,hc]
    rw [show Matrix.scalar (Fin 3) z = algebraMap F _ z by rfl]
    exact (Matrix.toLinAlgEquiv' (R := F)).commutes z
  let φ : E →ₐ[F] Matrix (Fin 3) (Fin 3) F :=
    Matrix.toLinAlgEquiv'.symm.toAlgHom.comp (action f z hf)
  have hφ : Function.Injective φ := φ.injective
  have hφlin (b : E) : Matrix.toLinAlgEquiv' (φ b) = action f z hf b := by
    simp only [φ,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply]
  have hroot : φ (AdjoinRoot.root (polynomial z))=g.val := by
    apply Matrix.toLinAlgEquiv'.injective
    rw [hφlin]
    exact action_root f z hf
  have hcomm (b : E) : Commute (φ b) g.val := by
    rw [←hroot]
    exact (Commute.all b _).map φ
  have hdet (b : E) : Matrix.det (φ b)=Algebra.norm F b := by
    rw [←LinearMap.det_toLin']
    change LinearMap.det (Matrix.toLinAlgEquiv' (φ b)) = _
    rw [hφlin]
    exact action_det f z hf hn (by simp) b
  let ν : Eˣ →* Fˣ := Units.map (Algebra.norm F)
  let N := ν.ker
  let C := (centralizer ({g} : Set (GL (Fin 3) F))).comap SpecialLinearGroup.toGL
  let j : N →* SL(3,F) :=
    { toFun := fun b => ⟨φ (b.val : E), by
        rw [hdet]
        exact congrArg Units.val b.property⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change φ ((a.val : E)*(b.val : E)) = φ (a.val : E)*φ (b.val : E)
        exact φ.map_mul _ _) }
  have hjC (b : N) : j b ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    apply Units.ext
    exact (hcomm (b.val : E)).eq
  let jC : N →* C := j.codRestrict C hjC
  have hjinj : Function.Injective jC := by
    intro b c h
    apply Subtype.ext
    apply Units.ext
    apply hφ
    exact congrArg (fun x : C => x.val.val) h
  have hjsurj : Function.Surjective jC := by
    intro c
    have hh : Commute f (Matrix.toLin' c.val.val) := by
      have he := (mem_centralizer_singleton_iff.mp c.property).symm
      have he' := congrArg (fun x : GL (Fin 3) F => Matrix.toLin' x.val) he
      change Matrix.toLinAlgEquiv' (g.val*c.val.val) = Matrix.toLinAlgEquiv' (c.val.val*g.val) at he'
      rw [map_mul,map_mul] at he'
      exact he'
    obtain ⟨b,hb⟩ := action_centralizer f z hf hn (by simp) (Matrix.toLin' c.val.val) hh
    have hb' : φ b=c.val.val := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [hφlin]
      exact hb
    have hb0 : b≠0 := by
      intro he
      have hzero : c.val.val=0 := by rw [←hb',he,map_zero]
      have hcd := c.val.property
      rw [hzero,det_zero] at hcd
      exact zero_ne_one hcd
    let u := Units.mk0 b hb0
    have hu : u ∈ N := by
      apply Units.ext
      change Algebra.norm F b=1
      rw [←hdet,hb']
      exact c.val.property
    refine ⟨⟨u,hu⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hb'
  let e : N ≃* C := MulEquiv.ofBijective jC ⟨hjinj,hjsurj⟩
  refine ⟨isCyclic_of_surjective e e.surjective,?_⟩
  rw [←Nat.card_congr e.toEquiv]
  have hcard := N.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr (FiniteField.unitsMap_norm_surjective F E),
    card_top,Nat.card_units,Nat.card_units,Module.natCard_eq_pow_finrank (K := F) (V := E),hdE] at hcard
  have hq : 1 < Nat.card F := Finite.one_lt_card
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card F - 1 by omega)
  rw [hcard]
  have hp : Nat.card F^3=(Nat.card F-1)*(Nat.card F^2+Nat.card F+1)+1 := by
    have hq' : Nat.card F=Nat.card F-1+1 := by omega
    calc
      _ = (Nat.card F-1+1)^3 := congrArg (fun n : ℕ => n^3) hq'
      _ = (Nat.card F-1)*((Nat.card F-1+1)^2+(Nat.card F-1+1)+1)+1 := by ring
      _ = _ := by rw [←hq']
  rw [mul_comm (Nat.card F^2+Nat.card F+1)]
  omega
end Matrices
end Matrix.CubicSinger

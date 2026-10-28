module
public import Theory.LinearAlgebra.CubicSingerCentralizer
public import Theory.LinearAlgebra.SplitSeparableEigenbasis
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.OddKernelInvolutionFibers
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# A fixed cubic plane for SL₃(4) automorphisms

An automorphism with cube one descends to the inner-diagonal subgroup of
Aut(PSL₃(4)), since its quotient has order dividing four. Lift it to an
actual GL₃ matrix whose cube is scalar. If that scalar has no cube root,
the Singer centralizer in SL₃ has order 21, so the automorphism fixes no
involution. Otherwise a split separable annihilator supplies an eigenbasis;
the determinant-one diagonal torus in this basis is a pointwise fixed E₉.

An inner involution has a unique involutory representative through the
scalar center of order three. Every commuting automorphism fixes this
representative, so the fixed-plane theorem applies to the marked pair.
The source consumer uses this plane and the original external cubic to
contradict the ambient three-rank bound.

The eigenbasis-to-matrix proof is adapted from the private
`split_cube_eigenbasis` in `Theory/LinearAlgebra/UnitaryCubicSplit.lean`.
The imported ATLAS results retain their attribution and license.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832, using the
linear scalar-cube calculation in A.3.18, printed pp.52--53.
-/

public noncomputable section
open Subgroup Matrix Polynomial
open scoped MatrixGroups IsMulCommutative
namespace Matrix.SL3.FourCubicFixedPlane
open Matrix.PSL3.OuterSolvable Matrix.PSL3.CartanActions
open Matrix.PSL3Four

private theorem cubic_linear (a : MulAut SL) (ha : a^3=1) :
    ∃ g : GL (Fin 3) F, linearConjSL F g = a := by
  let : (innerDiagonal F).Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← standard_eq_top_of_two_power_card F (m := 2) (by decide) card_F]
    exact standard_le_normalizer_innerDiagonal))
  let q := QuotientGroup.mk' (innerDiagonal F)
  have h3 : orderOf (q (centerAction F a)) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow,← map_pow,ha,map_one,map_one])
  have h4 : orderOf (q (centerAction F a)) ∣ 4 :=
    (_root_.orderOf_dvd_natCard _).trans OuterThreeStructure.diagonal_index_dvd_four
  have he : q (centerAction F a) = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 4) h3 h4)
  obtain ⟨g,hg⟩ := (QuotientGroup.eq_one_iff _).mp he
  exact ⟨g,ActorCoverage.centerAction_injective F hg⟩

private theorem split_eigenbasis (g : GL (Fin 3) F) (z : F)
    (hc : g.val^3=Matrix.scalar (Fin 3) z) (hz : z≠0) (a : F) (ha : a^3=z) :
    ∃ (P : GL (Fin 3) F) (d : Fin 3 → F),
      P.val*Matrix.diagonal d*P⁻¹.val=g.val := by
  classical
  obtain ⟨w,hw⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hw3 : orderOf w = 3 := by simpa [Nat.card_units,card_F] using hw
  have hpw : IsPrimitiveRoot (w : F) 3 := IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_injective (Units.coeHom F) Units.val_injective w).trans hw3)
  have ha0 : a≠0 := by intro h; apply hz; rw [←ha,h]; simp
  let p : F[X] := X^3-C z
  have hs : p.Splits := X_pow_sub_C_splits_of_isPrimitiveRoot hpw ha
  have hp : p.Separable := by
    rw [show p = ∏ i ∈ Finset.range 3, (X-C ((w:F)^i*a)) from
      X_pow_sub_C_eq_prod hpw (by decide) ha]
    apply separable_prod_X_sub_C_iff'.mpr
    intro i hi j hj he
    exact hpw.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      (mul_right_cancel₀ ha0 he)
  let f := Matrix.toLin' g.val
  have heval : aeval f p = 0 := by
    have he : aeval g.val p = 0 := by
      simp only [p,map_sub,map_pow,aeval_X,aeval_C]
      rw [hc]
      simp [Matrix.algebraMap_eq_diagonal,Matrix.scalar_apply]
    change aeval (Matrix.toLinAlgEquiv' (R := F) g.val) p = 0
    rw [aeval_algHom_apply,he,map_zero]
  obtain ⟨b,μ,hb⟩ := Module.End.exists_eigenbasis_of_split_separable_annihilator f p
    (monic_X_pow_sub_C _ (by decide)) hs hp heval
  have hdim : Module.finrank F (Fin 3 → F)=3 := by simp
  let b' := b.reindex (finCongr hdim)
  let d : Fin 3 → F := fun i => μ ((finCongr hdim).symm i)
  have hd : LinearMap.toMatrix b' b' f = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix_apply,b',d,Module.Basis.reindex_apply,hb]
    · simp [LinearMap.toMatrix_apply,b',d,Module.Basis.reindex_apply,hb,hij]
  let s := Pi.basisFun F (Fin 3)
  let P : GL (Fin 3) F := ⟨s.toMatrix b',b'.toMatrix s,
    s.toMatrix_mul_toMatrix_flip b',b'.toMatrix_mul_toMatrix_flip s⟩
  refine ⟨P,d,?_⟩
  change s.toMatrix b' * Matrix.diagonal d * b'.toMatrix s = g.val
  rw [←hd,basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  simp [s,f,LinearMap.toMatrix_eq_toMatrix']

/-- A cubic automorphism of the actual SL₃(4) fixing an involution fixes
an elementary abelian subgroup of order nine. -/
theorem exists_fixed_nine (a : MulAut SL) (ha : a^3=1)
    (t : SL) (ht : orderOf t=2) (hfix : a t=t) :
    ∃ E : Subgroup SL, IsElementaryAbelian 3 E ∧ Nat.card E=9 ∧
      ∀ x ∈ E, a x=x := by
  obtain ⟨g,rfl⟩ := cubic_linear a ha
  have hg : g^3 ∈ center (GL (Fin 3) F) := by
    rw [← Matrix.PSL3.ExtensionBorel.linearConj_ker]
    change linearConj F (g^3)=1
    rw [map_pow]
    change centerAction F (linearConjSL F g)^3=1
    rw [← map_pow,ha,map_one]
  obtain ⟨z,hz⟩ := GeneralLinearGroup.center_eq_range_scalar (n := Fin 3) (R := F) ▸ hg
  have hcube : g.val^3=Matrix.scalar (Fin 3) (z:F) :=
    (congrArg Units.val hz).symm
  have hroot : ∃ c : F, c^3=(z:F) := by
    by_contra! hn
    let C := (centralizer ({g} : Set (GL (Fin 3) F))).comap SpecialLinearGroup.toGL
    have hc : Nat.card C = 21 := by
      simpa only [card_F, Nat.reducePow, Nat.reduceAdd] using (Matrix.CubicSinger.matrix_centralizer g z hcube hn).2
    have htC : t ∈ C := by
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg SpecialLinearGroup.toGL hfix
      rw [linearConjSL_toGL] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hdiv : 2 ∣ 21 := by
      have hh := _root_.orderOf_dvd_natCard (⟨t,htC⟩ : C)
      have ho : orderOf (⟨t,htC⟩ : C)=2 := (Subgroup.orderOf_coe _).symm.trans ht
      simpa only [ho,hc] using hh
    norm_num at hdiv
  obtain ⟨c,hc⟩ := hroot
  obtain ⟨P,d,hd⟩ := split_eigenbasis g z hcube z.ne_zero c hc
  let f : Fˣ × Fˣ →* SL := (linearConjSL F P).toMonoidHom.comp (torusSL F)
  have hfi : Function.Injective f := (linearConjSL F P).injective.comp
    (BorelQuotient.torusSL_injective F)
  let : IsElementaryAbelian 3 (Fˣ × Fˣ) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      have hunit (y : Fˣ) : y^3=1 := by simpa [Nat.card_units,card_F] using pow_card_eq_one' (x := y)
      exact Prod.ext (hunit x.1) (hunit x.2) }
  let : IsElementaryAbelian 3 f.range := IsElementaryAbelian.of_injective
    (MonoidHom.ofInjective hfi).symm.toMonoidHom (MonoidHom.ofInjective hfi).symm.injective
  refine ⟨f.range,inferInstance,?_,?_⟩
  · rw [←Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv,Nat.card_prod,Nat.card_units,card_F]
  · rintro _ ⟨x,rfl⟩
    apply SpecialLinearGroup.toGL_injective
    rw [linearConjSL_toGL]
    apply mul_inv_eq_iff_eq_mul.mpr
    have hf : SpecialLinearGroup.toGL (f x) = P*SpecialLinearGroup.toGL (torusSL F x)*P⁻¹ :=
      linearConjSL_toGL F P _
    rw [hf]
    apply Units.ext
    change g.val*(P.val*(torusSL F x).val*P⁻¹.val)=
      (P.val*(torusSL F x).val*P⁻¹.val)*g.val
    have hcomm : Matrix.diagonal d * (torusSL F x).val =
        (torusSL F x).val * Matrix.diagonal d := by
      rw [torusSL_val,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    have hPi : P⁻¹.val * P.val = 1 := congrArg Units.val (inv_mul_cancel P)
    rw [←hd]
    calc
      _ = P.val * (Matrix.diagonal d * (torusSL F x).val) * P⁻¹.val := by
        simp only [Matrix.mul_assoc]
        rw [←Matrix.mul_assoc P⁻¹.val P.val,hPi,one_mul]
      _ = P.val * ((torusSL F x).val * Matrix.diagonal d) * P⁻¹.val := by rw [hcomm]
      _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [←Matrix.mul_assoc P⁻¹.val P.val,hPi,one_mul]
/-- The inner marked involution has a unique involutory representative
through the odd scalar center. A commuting cubic fixes that representative. -/
theorem exists_fixed_nine_of_commuting_inner_involution
    (a b : MulAut SL) (ha : a^3=1) (hb : orderOf b=2)
    (hbi : b ∈ MulAut.innerSubgroup SL) (hab : Commute a b) :
    ∃ E : Subgroup SL, IsElementaryAbelian 3 E ∧ Nat.card E=9 ∧
      ∀ x ∈ E, a x=x := by
  have hcenter : Nat.card (center SL)=3 := by
    rw [Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,card_F]
    norm_num
  have hc (x : SL) (hx : x ∈ center SL) : x^3=1 :=
    congrArg Subtype.val (hcenter ▸ pow_card_eq_one' (x := (⟨x,hx⟩ : center SL)))
  obtain ⟨u,hu⟩ := hbi
  have hb2 : b^2=1 := by simpa only [hb] using pow_orderOf_eq_one b
  have hu2 : u^2 ∈ center SL := by
    rw [←Theory.GroupTheory.DoubleCoverCentralizer.conj_kernel]
    change MulAut.conj (u^2)=1
    rw [map_pow,hu,hb2]
  let t := u^3
  have ht2 : t^2=1 := by
    dsimp only [t]
    rw [←pow_mul,show 3*2=2*3 from rfl,pow_mul]
    exact hc (u^2) hu2
  have htb : MulAut.conj t=b := by
    dsimp only [t]
    rw [map_pow,hu]
    exact (pow_succ b 2).trans (by rw [hb2,one_mul])
  have htn : t≠1 := by
    intro h
    have he : b=1 := htb.symm.trans (h ▸ map_one MulAut.conj)
    rw [he,orderOf_one] at hb
    omega
  have ht : orderOf t=2 := orderOf_eq_prime ht2 htn
  have hker : Nat.Coprime 2 (Nat.card (MulAut.conj : SL →* MulAut SL).ker) := by
    rw [Theory.GroupTheory.DoubleCoverCentralizer.conj_kernel,hcenter]
    decide
  have he : MulAut.conj t=MulAut.conj (a t) := by
    rw [htb]
    have hh : MulAut.conj (a t) = a*MulAut.conj t*a⁻¹ := by
      ext x
      simp
    rw [hh,htb,hab.eq,mul_inv_cancel_right]
  obtain ⟨k,hk⟩ := involutions_same_image_conj_ker MulAut.conj hker ht
    ((a.orderOf_eq t).trans ht) he
  have hkz : (k : SL) ∈ center SL := by
    simpa only [Theory.GroupTheory.DoubleCoverCentralizer.conj_kernel] using k.property
  have hat : a t=t := by
    rw [←hk,←mem_center_iff.mp hkz t,mul_inv_cancel_right]
  exact exists_fixed_nine a ha t ht hat

end Matrix.SL3.FourCubicFixedPlane

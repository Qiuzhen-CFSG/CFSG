module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverUnitaryBinary
public import Theory.LinearAlgebra.CubicSingerConjugacy

/-!
# Completing the linear-cover branch of the normal split-prime theorem

The same outside cubic cannot have a split scalar-cube implementer: an
eigenbasis would give a fixed elementary nine in the actual component,
contradicting the ambient three-rank bound. The nonsplit implementer generates
a cubic field, so its special-linear centralizer is the cyclic norm kernel
of order q²+q+1.

Every outside order-three subgroup has a generator in the original actor's
component coset. The corresponding matrix has exactly the same scalar cube.
Cubic-field coordinates and a norm determinant correction give an SL₃
conjugator, which lifts through the original marked action to the literal
subgroup conjugacy in H*. Thus the linear branch satisfies every clause of
A.3.18(3b). Only the unitary cover branch remains explicit in the reduction.

Source: Aschbacher–Smith A.3.18, printed pp.51–53. OddRankSource applies this
reduction to the original Cartan extension in 4.3.6, printed p.615.
-/

@[expose] public noncomputable section
open Subgroup Matrix Theory.GroupTheory Polynomial
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverSingerLinear

private theorem split_cube_eigenbasis {F : Type*} [Field F]
    (g : GL (Fin 3) F) (z w a : F) (hw : IsPrimitiveRoot w 3)
    (hcube : g.val^3=Matrix.scalar (Fin 3) z) (ha : a^3=z) (ha0 : a≠0) :
    ∃ (P : GL (Fin 3) F) (d : Fin 3 → F),
      P.val*Matrix.diagonal d*P⁻¹.val=g.val := by
  classical
  let p : F[X] := X^3-C z
  have hs : p.Splits := X_pow_sub_C_splits_of_isPrimitiveRoot hw ha
  have hp : p.Separable := by
    rw [show p = ∏ i ∈ Finset.range 3, (X-C (w^i*a)) from
      X_pow_sub_C_eq_prod hw (by decide) ha]
    apply separable_prod_X_sub_C_iff'.mpr
    intro i hi j hj he
    exact hw.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      (mul_right_cancel₀ ha0 he)
  let f := Matrix.toLin' g.val
  have heval : aeval f p = 0 := by
    have he : aeval g.val p = 0 := by
      simp only [p,map_sub,map_pow,aeval_X,aeval_C]
      rw [hcube]
      simp [Matrix.algebraMap_eq_diagonal,Matrix.scalar_apply]
    change aeval (Matrix.toLinAlgEquiv' (R := F) g.val) p = 0
    rw [aeval_algHom_apply,he,map_zero]
  obtain ⟨b,μ,hb⟩ := Module.End.exists_eigenbasis_of_split_separable_annihilator f p (monic_X_pow_sub_C _ (by decide)) hs hp heval
  have hdim : Module.finrank F (Fin 3 → F)=3 := by simp
  let b' := b.reindex (finCongr hdim)
  let d : Fin 3 → F := fun i => μ ((finCongr hdim).symm i)
  have hd : LinearMap.toMatrix b' b' f = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix_apply,b',d,Module.Basis.reindex_apply,hb]
    · simp [LinearMap.toMatrix_apply,b',d,Module.Basis.reindex_apply,hb,
        hij]
  let s := Pi.basisFun F (Fin 3)
  let P : GL (Fin 3) F := ⟨s.toMatrix b',b'.toMatrix s,
    s.toMatrix_mul_toMatrix_flip b',b'.toMatrix_mul_toMatrix_flip s⟩
  refine ⟨P,d,?_⟩
  change s.toMatrix b' * Matrix.diagonal d * b'.toMatrix s = g.val
  rw [←hd,basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  simp [s,f,LinearMap.toMatrix_eq_toMatrix']


private theorem split_cube_rank {F : Type*} [Field F] [Finite F]
    (g : GL (Fin 3) F) (z : Fˣ) (w a : F) (hw : IsPrimitiveRoot w 3)
    (hc : g^3=GeneralLinearGroup.scalar (Fin 3) z) (ha : a^3=(z:F)) :
    2 ≤ primeRank 3 ((centralizer ({g}:Set (GL (Fin 3) F))).comap SpecialLinearGroup.toGL) := by
  have ha0 : a≠0 := by intro he; rw [he,zero_pow (by decide)] at ha; exact z.ne_zero ha.symm
  obtain ⟨P,d,hP⟩ := split_cube_eigenbasis g z w a hw (congrArg Units.val hc) ha ha0
  have hcoord : ((MulAut.conj P⁻¹) g).val=diagonal d := by
    change P⁻¹.val*g.val*P.val=diagonal d
    rw [←hP]
    simp only [←mul_assoc,Units.inv_mul_cancel_right,Units.inv_mul,one_mul]
  let C := (centralizer ({g}:Set (GL (Fin 3) F))).comap SpecialLinearGroup.toGL
  have hmem (s : SL(3,F)) (v : Fin 3 → F) (hs : s.val=diagonal v) :
      Matrix.PSL3.OuterSolvable.linearConjSL F P s ∈ C := by
    have hh : Commute (SpecialLinearGroup.toGL s) ((MulAut.conj P⁻¹) g) := by
      apply Units.ext
      change s.val*((MulAut.conj P⁻¹) g).val=((MulAut.conj P⁻¹) g).val*s.val
      rw [hcoord,hs,diagonal_mul_diagonal,diagonal_mul_diagonal]
      congr 1
      ext i
      exact mul_comm _ _
    apply mem_centralizer_singleton_iff.mpr
    rw [Matrix.PSL3.OuterSolvable.linearConjSL_toGL]
    have hh' := hh.map (MulAut.conj P).toMonoidHom
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,
      mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh'.eq
  have hw3 : w^3=1 := hw.pow_eq_one
  have hw1 : w≠1 := hw.ne_one (by decide)
  let D := Theory.SpecificGroups.SignedThreeCubicRank.diagonal w hw3
  let Z := Theory.SpecificGroups.SignedThreeCubicRank.scalar w hw3
  have hD : Matrix.PSL3.OuterSolvable.linearConjSL F P D ∈ C := by
    apply hmem D ![1,w,w^2]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hZ : Matrix.PSL3.OuterSolvable.linearConjSL F P Z ∈ C :=
    hmem Z (fun _ => w) rfl
  let f := (MulAut.conj P⁻¹).toMonoidHom.comp (SpecialLinearGroup.toGL.comp C.subtype)
  have hf : Function.Injective f := (MulAut.conj P⁻¹).injective.comp
    (SpecialLinearGroup.toGL_injective.comp C.subtype_injective)
  apply Theory.SpecificGroups.SignedThreeCubicRank.special_rank w hw3 hw1 f hf
    ⟨_,hD⟩ ⟨_,hZ⟩
  all_goals
    change P⁻¹*SpecialLinearGroup.toGL (Matrix.PSL3.OuterSolvable.linearConjSL F P _)*P = _
    rw [Matrix.PSL3.OuterSolvable.linearConjSL_toGL]
    group
    rfl

private theorem cubic_scalar {F : Type*} [Field F] (g : GL (Fin 3) F)
    (h : Matrix.PSL3.OuterSolvable.linearConjSL F g ^ 3=1) :
    ∃ z : Fˣ, g^3=GeneralLinearGroup.scalar (Fin 3) z := by
  have hs : Matrix.PSL3.OuterSolvable.linearConjSL F (g^3)=1 := by rwa [map_pow]
  have hc (s : SL(3,F)) : g^3*SpecialLinearGroup.toGL s=SpecialLinearGroup.toGL s*g^3 := by
    have he := congrArg SpecialLinearGroup.toGL (DFunLike.congr_fun hs s)
    rw [Matrix.PSL3.OuterSolvable.linearConjSL_toGL] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hz : g^3 ∈ center (GL (Fin 3) F) := by
    apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    exact (congrArg Units.val (hc ⟨t.toMatrix,by simp⟩)).symm
  rw [GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨z,hz⟩ := hz
  exact ⟨z,hz.symm⟩

private def centralizerEquiv {G F : Type*} [Group G] [Field F]
    (K : Subgroup G) [K.Normal] (a : G) (e : K ≃* SL(3,F)) (g : GL (Fin 3) F)
    (hmark : ∀ k : K, SpecialLinearGroup.toGL (e (MulAut.conjNormal a k)) =
      g*SpecialLinearGroup.toGL (e k)*g⁻¹) :
    ((centralizer ({a}:Set G)).comap K.subtype) ≃*
      ((centralizer ({g}:Set (GL (Fin 3) F))).comap SpecialLinearGroup.toGL) := by
  let C := (centralizer ({a}:Set G)).comap K.subtype
  let D := (centralizer ({g}:Set (GL (Fin 3) F))).comap SpecialLinearGroup.toGL
  have hm (k : K) : k∈C ↔ e k∈D := by
    change (k:G) ∈ centralizer ({a}:Set G) ↔ SpecialLinearGroup.toGL (e k) ∈ centralizer ({g}:Set (GL (Fin 3) F))
    rw [mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
    constructor
    · intro h
      have he : (MulAut.conjNormal a : MulAut K) k=k :=
        Subtype.ext (mul_inv_eq_iff_eq_mul.mpr h.symm)
      have hh := hmark k
      rw [he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    · intro h
      have he : (MulAut.conjNormal a : MulAut K) k=k := by
        apply e.injective
        apply SpecialLinearGroup.toGL_injective
        exact (hmark k).trans (mul_inv_eq_iff_eq_mul.mpr h.symm)
      exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm
  exact
    { toFun := fun c => ⟨e c.val,(hm _).mp c.property⟩
      invFun := fun d => ⟨e.symm d.val,(hm _).mpr (by simpa only [e.apply_symm_apply] using d.property)⟩
      left_inv c := Subtype.ext (e.symm_apply_apply _)
      right_inv d := Subtype.ext (e.apply_symm_apply _)
      map_mul' c d := Subtype.ext (e.map_mul _ _) }

private theorem nonsplit_marking {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (K : Subgroup G) [K.Normal] (a : G) (ha : orderOf a=3) (haK : a∉K)
    (hr : primeRank 3 G≤2) (e : K ≃* SL(3,F)) (g : GL (Fin 3) F)
    (hmark : ∀ k : K, SpecialLinearGroup.toGL (e (MulAut.conjNormal a k)) =
      g*SpecialLinearGroup.toGL (e k)*g⁻¹) (hdiv : 3 ∣ Nat.card F-1) :
    ∃ z : Fˣ, g^3=GeneralLinearGroup.scalar (Fin 3) z ∧ ∀ b : F, b^3≠(z:F) := by
  let C := (centralizer ({a}:Set G)).comap K.subtype
  let D := (centralizer ({g}:Set (GL (Fin 3) F))).comap SpecialLinearGroup.toGL
  let E : C ≃* D := centralizerEquiv K a e g hmark
  have hα : Matrix.PSL3.OuterSolvable.linearConjSL F g = MulAut.congr e (MulAut.conjNormal a) := by
    apply MulEquiv.ext
    intro s
    obtain ⟨k,rfl⟩ := e.surjective s
    apply SpecialLinearGroup.toGL_injective
    rw [Matrix.PSL3.OuterSolvable.linearConjSL_toGL]
    simpa only [MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply] using (hmark k).symm
  have ha3 : a^3=1 := by simpa only [ha] using pow_orderOf_eq_one a
  obtain ⟨z,hz⟩ := cubic_scalar g (by
    rw [hα,←map_pow,←map_pow,ha3,map_one,map_one])
  obtain ⟨w,hw⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rwa [Nat.card_units])
  have hw' : IsPrimitiveRoot (w:F) 3 := by
    rw [IsPrimitiveRoot.iff_orderOf,orderOf_units]
    exact hw
  have hn : ∀ b : F, b^3≠(z:F) := by
    intro b hb
    have hD := split_cube_rank g z w b hw' hz hb
    have hC : 2≤primeRank 3 C := by rwa [←primeRank_congr 3 E] at hD
    let j : C →* G := K.subtype.comp C.subtype
    have hj : Function.Injective j := K.subtype_injective.comp C.subtype_injective
    have hCeq : primeRank 3 C=2 := by
      have hh := (Theory.GroupTheory.primeRank_le_of_injective 3 j hj).trans hr
      omega
    obtain ⟨B,hB,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := C) (p := 3)
    let := hB
    let B' := B.map j
    let : IsElementaryAbelian 3 B' := IsElementaryAbelian.map j
    have hB'K : B'≤K := by rintro _ ⟨v,_,rfl⟩; exact v.val.property
    have hfix : B'≤centralizer ({a}:Set G) := by
      rintro _ ⟨v,_,rfl⟩
      exact v.property
    have hcard' : Nat.card B'=3^2 := by rw [card_map_of_injective hj,hcard,hCeq]
    have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join B' a ha
      (fun h => haK (hB'K h)) hfix hcard'
    omega
  exact ⟨z,hz,hn⟩

/-- The centralizer of the actual outside linear-cover cubic is cyclic with
precisely the Singer order. No matrix irreducibility is assumed. -/
theorem linear_centralizer {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (a : G) (ha : orderOf a=3) (haK : a∉K)
    (hr : primeRank 3 G≤2) (q : ℕ) (hq : SignedCongruence false q)
    (hdiag : IsLinearDiagonal K q (MulAut.conjNormal a)) :
    IsCyclic ((centralizer ({a}:Set G)).comap K.subtype) ∧
      Nat.card ((centralizer ({a}:Set G)).comap K.subtype)=q^2+q+1 := by
  obtain ⟨F,_,_,hF,e,g,hmark⟩ := hdiag
  have hdiv : 3 ∣ Nat.card F-1 := by
    rw [hF]
    change q%3=1 at hq
    exact Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨z,hz,hn⟩ := nonsplit_marking K a ha haK hr e g hmark hdiv
  let E := centralizerEquiv K a e g hmark
  obtain ⟨hcyc,hcard⟩ := Matrix.CubicSinger.matrix_centralizer g z (congrArg Units.val hz) hn
  let := hcyc
  refine ⟨isCyclic_of_injective E.toMonoidHom E.injective,?_⟩
  rw [Nat.card_congr E.toEquiv,hcard,hF]

private theorem coset_cubic_conjugate {G F : Type*} [Group G] [Field F] [Finite F]
    (K : Subgroup G) [K.Normal] (a : G) (ha : a^3=1)
    (e : K ≃* SL(3,F)) (g : GL (Fin 3) F)
    (hmark : ∀ k : K, SpecialLinearGroup.toGL (e (MulAut.conjNormal a k)) =
      g*SpecialLinearGroup.toGL (e k)*g⁻¹)
    (z : Fˣ) (hz : g^3=GeneralLinearGroup.scalar (Fin 3) z)
    (hn : ∀ b : F, b^3≠(z:F)) (k : K) (hk : ((k:G)*a)^3=1) :
    ∃ l : K, (l:G)*a*(l:G)⁻¹=(k:G)*a := by
  let α : MulAut K := MulAut.conjNormal a
  have hprod : k*α k*(MulAut.conjNormal (a^2) k)=1 := by
    apply K.subtype_injective
    change (k:G)*(a*(k:G)*a⁻¹)*(a^2*(k:G)*(a^2)⁻¹)=1
    calc
      _ = ((k:G)*a)^3*(a^3)⁻¹ := by
        simp only [pow_succ,pow_zero]
        group
      _ = 1 := by rw [hk,ha]; simp
  have hmark2 : SpecialLinearGroup.toGL (e (MulAut.conjNormal (a^2) k))=
      g^2*SpecialLinearGroup.toGL (e k)*(g^2)⁻¹ := by
    have he : (MulAut.conjNormal (a^2) : MulAut K) k=α (α k) := by
      rw [map_pow,pow_two,MulAut.mul_apply]
    rw [he,hmark,hmark]
    simp only [pow_two]
    group
  let A := SpecialLinearGroup.toGL (e k)
  have hprod' : A*(g*A*g⁻¹)*(g^2*A*(g^2)⁻¹)=1 := by
    have hh := congrArg (fun t : K => SpecialLinearGroup.toGL (e t)) hprod
    simpa only [map_mul,map_one,α,hmark,hmark2] using hh
  have hcube : (A*g)^3=g^3 := by
    calc
      _ = (A*(g*A*g⁻¹)*(g^2*A*(g^2)⁻¹))*g^3 := by
        simp only [pow_succ,pow_zero]
        group
      _ = g^3 := by rw [hprod',one_mul]
  obtain ⟨P,hP⟩ := Matrix.CubicSinger.special_conjugate_of_same_cube g (A*g) z
    (congrArg Units.val hz) (congrArg Units.val (hcube.trans hz)) hn
  let l := e.symm P
  have hl : l*(α l)⁻¹=k := by
    apply e.injective
    apply SpecialLinearGroup.toGL_injective
    simp only [map_mul,map_inv,α,hmark,show e l=P from e.apply_symm_apply P]
    calc
      _ = SpecialLinearGroup.toGL P*g*(SpecialLinearGroup.toGL P)⁻¹*g⁻¹ := by group
      _ = A := by rw [hP]; group
  refine ⟨l,?_⟩
  have hh := congrArg (fun t : K => (t:G)*a) hl
  change ((l:G)*(a*(l:G)*a⁻¹)⁻¹)*a=(k:G)*a at hh
  convert hh using 1
  group

private theorem exists_coset_generator {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (a : G) (ha : orderOf a=3)
    (hgen : K ⊔ zpowers a=⊤) (X : Subgroup G) (hX : Nat.card X=3) (hXK : ¬ X≤K) :
    ∃ k : K, ((k:G)*a)^3=1 ∧ X=zpowers ((k:G)*a) := by
  classical
  have ha3 : a^3=1 := by simpa only [ha] using pow_orderOf_eq_one a
  obtain ⟨b,hbX,hbK⟩ := Set.not_subset.mp hXK
  have hb3 : b^3=1 := by
    have hh : (⟨b,hbX⟩ : X)^Nat.card X=1 := pow_card_eq_one'
    rw [hX] at hh
    exact congrArg Subtype.val hh
  have hgenerator (c : G) (hcX : c∈X) (hcK : c∉K) (hc3 : c^3=1) : X=zpowers c := by
    have hc1 : c≠1 := fun h => hcK (h ▸ K.one_mem)
    have hco : orderOf c=3 := orderOf_eq_prime hc3 hc1
    apply (eq_of_le_of_card_ge (zpowers_le.mpr hcX) ?_).symm
    rw [Nat.card_zpowers,hco,hX]
  obtain ⟨k,hk,v,hv,hkv⟩ := mem_sup_of_normal_left.mp (show b∈K ⊔ zpowers a by rw [hgen]; trivial)
  rw [mem_zpowers_iff_mem_range_orderOf,ha] at hv
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  have hi' : i<3 := Finset.mem_range.mp hi
  interval_cases i
  · have he : k=b := by simpa using hkv
    exact (hbK (he ▸ hk)).elim
  · have he : k*a=b := by simpa using hkv
    refine ⟨⟨k,hk⟩,?_,?_⟩
    · simpa only [he] using hb3
    · simpa only [he] using hgenerator b hbX hbK hb3
  · let k' : K := MulAut.conjNormal a (⟨k,hk⟩ : K)⁻¹
    have haInv : (a^2)⁻¹=a := by
      apply inv_eq_of_mul_eq_one_right
      rw [←pow_succ,ha3]
    have he : (k':G)*a=b⁻¹ := by
      rw [←hkv,_root_.mul_inv_rev,haInv]
      change (a*k⁻¹*a⁻¹)*a=a*k⁻¹
      group
    have hbInv3 : (b⁻¹)^3=1 := by rw [inv_pow,hb3,inv_one]
    refine ⟨k',?_,?_⟩
    · simpa only [he] using hbInv3
    · simpa only [he] using hgenerator b⁻¹ (X.inv_mem hbX)
        (fun h => hbK (by simpa using K.inv_mem h)) hbInv3

/-- Every outside subgroup of order three is conjugate under the actual
linear cover to the subgroup generated by the original actor. -/
theorem linear_fusion {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (a : G) (ha : orderOf a=3) (haK : a∉K)
    (hr : primeRank 3 G≤2) (hgen : K ⊔ zpowers a=⊤)
    (q : ℕ) (hq : SignedCongruence false q)
    (hdiag : IsLinearDiagonal K q (MulAut.conjNormal a)) :
    ∀ X : Subgroup G, Nat.card X=3 → ¬ X≤K →
      ∃ l : K, X.map (MulAut.conj l.val).toMonoidHom=zpowers a := by
  obtain ⟨F,_,_,hF,e,g,hmark⟩ := hdiag
  have hdiv : 3 ∣ Nat.card F-1 := by
    rw [hF]
    change q%3=1 at hq
    exact Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨z,hz,hn⟩ := nonsplit_marking K a ha haK hr e g hmark hdiv
  intro X hX hXK
  obtain ⟨k,hk,hXeq⟩ := exists_coset_generator K a ha hgen X hX hXK
  have ha3 : a^3=1 := by simpa only [ha] using pow_orderOf_eq_one a
  obtain ⟨l,hl⟩ := coset_cubic_conjugate K a ha3 e g hmark z hz hn k hk
  refine ⟨l⁻¹,?_⟩
  rw [hXeq,MonoidHom.map_zpowers]
  congr 1
  simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,Subgroup.coe_inv,inv_inv]
  rw [←hl]
  group

open CFSG.Quasithin.Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The only remaining cover branch is unitary. It retains the literal star
quotient, the original cubic, the residual product and disjoint complement. -/
structure UnitaryStarCover (K : Subgroup G) (a : G) : Prop extends
    CoverStructure.StarCover K a where
  marking : ∃ q : ℕ, CoverParameter true q ∧ SignedCongruence true q ∧
    IsSU (starComponent 3 K) 3 q ∧ ∃ α : MulAut (starComponent 3 K),
      (∀ l : starComponent 3 K, (α l).val=starMap 3 G a*l.val*(starMap 3 G a)⁻¹) ∧
      α∉MulAut.innerSubgroup (starComponent 3 K) ∧ IsUnitaryDiagonal (starComponent 3 K) q α

/-- The linear-cover branch of A.3.18 is complete, including its exact
centralizer and conjugacy of every outside subgroup of order three. -/
theorem alternatives_or_unitary_star_cover
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {K : Subgroup G} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : G) (ha : orderOf a=p) (haK : a∉K) (hgen : K ⊔ zpowers a=⊤) :
    Alternatives p K ∨ (p=3 ∧ UnitaryStarCover K a) := by
  rcases CoverUnitaryBinary.alternatives_or_marked_star_cover hG hK hp ho hr a ha haK hgen with
    halt | ⟨rfl,hs⟩
  · exact Or.inl halt
  obtain ⟨u,q,hq,hmod,hm,α,hact,houter,hdiag⟩ := hs.marking
  cases u with
  | true => exact Or.inr ⟨rfl,hs.toStarCover,q,hq,hmod,hm,α,hact,houter,hdiag⟩
  | false =>
    let : (starComponent 3 K).Normal :=
      (inferInstance : K.Normal).map _ (QuotientGroup.mk'_surjective _)
    have he : α=(MulAut.conjNormal (starMap 3 G a) : MulAut (starComponent 3 K)) := by
      apply MulEquiv.ext
      intro l
      exact Subtype.ext (hact l)
    have hdiag' : IsLinearDiagonal (starComponent 3 K) q
        (MulAut.conjNormal (starMap 3 G a)) := by simpa [IsDiagonalSign,he] using hdiag
    have hb : primeRank 3 (Star 3 G)≤2 :=
      (primeRank_quotient_le_of_coprime 3 (pPrimeCore 3 G) pPrimeCore_coprime_card).trans
        (hG.stronglyQuasithin 3 Nat.prime_three (by decide))
    have hjoin : starComponent 3 K ⊔ zpowers (starMap 3 G a)=⊤ := by
      have hh := congrArg (Subgroup.map (starMap 3 G)) hgen
      rw [Subgroup.map_sup,MonoidHom.map_zpowers,
        map_top_of_surjective (starMap 3 G) (QuotientGroup.mk'_surjective _)] at hh
      exact hh
    obtain ⟨hcyc,hcard⟩ := linear_centralizer (starComponent 3 K) (starMap 3 G a)
      hs.order hs.outside hb q hmod hdiag'
    have hfus := linear_fusion (starComponent 3 K) (starMap 3 G a)
      hs.order hs.outside hb hjoin q hmod hdiag'
    exact Or.inl (Or.inr (Or.inr ⟨rfl,Or.inl ⟨false,q,hmod,hm⟩,
      Or.inr ⟨false,q,hmod,hm,starMap 3 G a,α,hs.order,hact,houter,hdiag,
        hs.residual,hs.disjoint,hcyc,hcard,hfus⟩⟩))

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverSingerLinear

module
public import Theory.LinearAlgebra.UnitaryCubicSinger
public import Theory.LinearAlgebra.CubicSingerConjugacy
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus

/-!
# Special-unitary conjugacy of nonsplit scalar cubes

The linear conjugator transports the original Hermitian form. Its form
ratio is a self-adjoint element of the cubic centralizer field. Surjectivity
of the quadratic power norm corrects that ratio inside the centralizer,
producing a unitary conjugator in every characteristic. The full unitary
centralizer has order q³+1; its determinant kernel is the special centralizer
of order q²−q+1. Thus it realizes every norm-one determinant, and a final
commuting correction gives a special-unitary conjugator.

Source: the Singer-orbit argument in Aschbacher–Smith A.3.18, printed p.53.
The original matrices and the original Hermitian form are retained throughout.
-/

@[expose] public noncomputable section
open Matrix Polynomial Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant
open HermitianForm HermitianForm.EvenInner
namespace Matrix.UnitarySinger
variable {F : Type*} [Field F]

private theorem power_norm_surjective {E : Type*} [Field E] [Finite E]
    (t : ℕ) (ht : 1<t) (hc : Nat.card E=t^2) (a : Eˣ) (ha : a^t=a) :
    ∃ b : Eˣ, b^(t+1)=a := by
  let f := powMonoidHom (t+1) (α := Eˣ)
  let N := rootsOfUnity (t-1) E
  have hcard : Nat.card Eˣ=(t-1)*(t+1) := by
    rw [Nat.card_units,hc]
    simpa only [one_pow,mul_comm] using Nat.sq_sub_sq t 1
  have hle : f.range≤N := by
    rintro _ ⟨u,rfl⟩
    rw [mem_rootsOfUnity]
    change (u^(t+1))^(t-1)=1
    rw [←pow_mul,mul_comm,←hcard]
    exact pow_card_eq_one'
  have hfc : Nat.card f.range=t-1 := by
    rw [IsCyclic.card_powMonoidHom_range,hcard,Nat.gcd_eq_right (dvd_mul_left _ _),
      Nat.mul_div_cancel _ (by omega : 0<t+1)]
  have hNc : Nat.card N=t-1 := by
    dsimp only [N]
    rw [rootsOfUnity_eq_ker,IsCyclic.card_powMonoidHom_ker,hcard,Nat.gcd_eq_right (dvd_mul_right _ _)]
  have he : f.range=N := eq_of_le_of_card_ge hle (by rw [hfc,hNc])
  have haN : a∈N := by
    rw [mem_rootsOfUnity]
    apply mul_right_cancel (b := a)
    rw [←pow_succ,show t-1+1=t by omega,ha,one_mul]
  obtain ⟨b,hb⟩ := (he.symm ▸ haN : a∈f.range)
  exact ⟨b,hb⟩

/-- The adjoint of the multiplication operator is middle Frobenius on its field coefficient. -/
theorem units_adjoint [Finite F] {p n : ℕ} [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (hn : 0<n)
    (hcard : Nat.card F=(p^n)^2) (hconj : ∀ x, J.conj x=x^(p^n))
    (hdiv : 3 ∣ p^n+1) (g : J.unitarySubgroup)
    (z : Fˣ) (hz : J.conj (z:F)*z=1)
    (hc : g.val.val^3=Matrix.scalar (Fin 3) (z:F))
    (hnonsplit : ∀ a : F, a^3≠(z:F))
    (u : (AdjoinRoot (CubicSinger.polynomial (z:F)))ˣ) :
    adjoint J (Units.map (matrixAction g.val z hc).toMonoidHom u)=
      Units.map (matrixAction g.val z hc).toMonoidHom (u^((p^n)^3)) := by
  let φ := matrixAction g.val (z:F) hc
  apply Units.ext
  rw [adjoint_val]
  change J.form⁻¹*J.conjTranspose (φ (u:_))*J.form=φ ((u:_)^((p^n)^3))
  rw [mul_assoc,action_adjoint J hn hcard hconj hdiv g z hz hc hnonsplit]
  rw [←mul_assoc,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr J.form_nondegenerate),one_mul]

/-- Same-cube linear conjugacy has a unitary correction over either characteristic. -/
theorem unitary_conjugate_of_same_cube [Finite F] {p n : ℕ} [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (hn : 0<n)
    (hcard : Nat.card F=(p^n)^2) (hconj : ∀ x, J.conj x=x^(p^n))
    (hdiv : 3 ∣ p^n+1) (g h : J.unitarySubgroup)
    (z : Fˣ) (hz : J.conj (z:F)*z=1)
    (hg : g.val.val^3=Matrix.scalar (Fin 3) (z:F))
    (hh : h.val.val^3=Matrix.scalar (Fin 3) (z:F))
    (hnonsplit : ∀ a : F, a^3≠(z:F)) :
    ∃ P : J.unitarySubgroup, P.val*g.val*P.val⁻¹=h.val := by
  obtain ⟨D,hD⟩ := CubicSinger.conjugate_of_same_cube g.val h.val (z:F) hg hh hnonsplit
  have hD' : D*g.val=h.val*D := mul_inv_eq_iff_eq_mul.mp hD
  let a := adjoint J D*D
  have ha : adjoint J a=a := by dsimp only [a]; rw [adjoint_mul,adjoint_twice]
  have hag : Commute a g.val := by
    have he := congrArg (adjoint J) hD'
    rw [adjoint_mul,adjoint_mul,(mem_unitary_iff_adjoint J g.val).mp g.property,
      (mem_unitary_iff_adjoint J h.val).mp h.property] at he
    have he' := congrArg (fun X => g.val*X*h.val) he
    have had : adjoint J D*h.val=g.val*adjoint J D := by
      simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel,mul_one] using he'
    change (adjoint J D*D)*g.val=g.val*(adjoint J D*D)
    rw [mul_assoc,hD',←mul_assoc,had,mul_assoc]
  let E := AdjoinRoot (CubicSinger.polynomial (z:F))
  let : Fact (Irreducible (CubicSinger.polynomial (z:F))) :=
    ⟨CubicSinger.irreducible_polynomial (z:F) hnonsplit⟩
  let : Field E := inferInstance
  have hdE : Module.finrank F E=3 := CubicSinger.cubic_finrank (z:F)
  let : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let : Finite E := (Module.finite_iff_finite (R := F) (M := E)).mp inferInstance
  let φ := matrixAction g.val (z:F) hg
  let U : Eˣ →* GL (Fin 3) F := Units.map φ.toMonoidHom
  have hUinj : Function.Injective U := by
    intro u v huv
    apply Units.ext
    apply φ.injective
    exact congrArg Units.val huv
  obtain ⟨u,hu⟩ := exists_matrixAction g.val a (z:F) hg hnonsplit hag
  have hufix : u^((p^n)^3)=u := by
    apply hUinj
    change Units.map φ.toMonoidHom _=Units.map φ.toMonoidHom u
    rw [←units_adjoint J hn hcard hconj hdiv g z hz hg hnonsplit u,hu,ha]
  have hE : Nat.card E=((p^n)^3)^2 := by
    rw [Module.natCard_eq_pow_finrank (K := F),hdE,hcard]
    ring
  have hq : 1<p^n := Nat.one_lt_pow hn.ne' (Fact.out : p.Prime).one_lt
  obtain ⟨v,hv⟩ := power_norm_surjective ((p^n)^3) (by nlinarith) hE u hufix
  let B := U v
  have hBnorm : adjoint J B*B=a := by
    rw [show adjoint J B=U (v^((p^n)^3)) from units_adjoint J hn hcard hconj hdiv g z hz hg hnonsplit v,
      ←map_mul,←pow_succ,hv]
    exact hu
  have hBg : Commute B g.val := by
    apply Units.ext
    change φ (v:E)*g.val.val=g.val.val*φ (v:E)
    rw [←matrixAction_root g.val (z:F) hg]
    exact (Commute.all (v:E) _).map φ
  let P := D*B⁻¹
  have hP : P∈J.unitarySubgroup := by
    rw [mem_unitary_iff_adjoint,eq_inv_iff_mul_eq_one]
    change adjoint J (D*B⁻¹)*(D*B⁻¹)=1
    rw [adjoint_mul,adjoint_inv,mul_assoc,←mul_assoc (adjoint J D) D,
      show adjoint J D*D=a from rfl,←hBnorm]
    group
  refine ⟨⟨P,hP⟩,?_⟩
  change (D*B⁻¹)*g.val*(D*B⁻¹)⁻¹=h.val
  calc
    _ = D*(B⁻¹*g.val*B)*D⁻¹ := by group
    _ = D*g.val*D⁻¹ := by rw [hBg.inv_left.eq]; group
    _ = h.val := hD
/-- The unitary centralizer of this nonsplit cubic realizes every norm-one determinant. -/
theorem exists_unitary_commuting_det [Finite F] {p n : ℕ} [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (hn : 0<n)
    (hcard : Nat.card F=(p^n)^2) (hconj : ∀ x, J.conj x=x^(p^n))
    (hdiv : 3 ∣ p^n+1) (g : J.unitarySubgroup)
    (z : Fˣ) (hz : J.conj (z:F)*z=1)
    (hc : g.val.val^3=Matrix.scalar (Fin 3) (z:F))
    (hnonsplit : ∀ a : F, a^3≠(z:F))
    (d : Fˣ) (hd : J.conj (d:F)*d=1) :
    ∃ c : J.unitarySubgroup, Commute c.val g.val ∧ GeneralLinearGroup.det c.val=d := by
  classical
  let q := p^n
  have hq : 1<q := Nat.one_lt_pow hn.ne' (Fact.out : p.Prime).one_lt
  let E := AdjoinRoot (CubicSinger.polynomial (z:F))
  let : Fact (Irreducible (CubicSinger.polynomial (z:F))) :=
    ⟨CubicSinger.irreducible_polynomial (z:F) hnonsplit⟩
  let : Field E := inferInstance
  have hdE : Module.finrank F E=3 := CubicSinger.cubic_finrank (z:F)
  let : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let : Finite E := (Module.finite_iff_finite (R := F) (M := E)).mp inferInstance
  have hE : Nat.card E=(q^3)^2 := by
    rw [Module.natCard_eq_pow_finrank (K := F),hdE,hcard]
    dsimp [q]; ring
  let φ := matrixAction g.val (z:F) hc
  let U : Eˣ →* GL (Fin 3) F := Units.map φ.toMonoidHom
  let N := rootsOfUnity (q^3+1) E
  let C := (Subgroup.centralizer ({g.val}:Set (GL (Fin 3) F))).comap J.unitarySubgroup.subtype
  have hUunit (u : N) : U u.val∈J.unitarySubgroup :=
    (matrixAction_unitary_iff J hn hcard hconj hdiv g z hz hc hnonsplit u.val).mpr
      ((mem_rootsOfUnity _ _).mp u.property)
  have hcomm (u : Eˣ) : Commute (U u) g.val := by
    apply Units.ext
    change φ (u:E)*g.val.val=g.val.val*φ (u:E)
    rw [←matrixAction_root g.val (z:F) hc]
    exact (Commute.all (u:E) _).map φ
  let j : N →* C :=
    { toFun := fun u => ⟨⟨U u.val,hUunit u⟩,mem_centralizer_singleton_iff.mpr (hcomm u.val).eq⟩
      map_one' := Subtype.ext (Subtype.ext (U.map_one))
      map_mul' := fun u v => Subtype.ext (Subtype.ext (U.map_mul u.val v.val)) }
  have hjinj : Function.Injective j := by
    intro u v h
    apply Subtype.ext
    apply Units.ext
    apply φ.injective
    exact congrArg (fun x : C => x.val.val.val) h
  have hjsurj : Function.Surjective j := by
    intro c
    obtain ⟨u,hu⟩ := exists_matrixAction g.val c.val.val (z:F) hc hnonsplit
      (mem_centralizer_singleton_iff.mp c.property)
    have huN : u∈N := (mem_rootsOfUnity _ _).mpr
      ((matrixAction_unitary_iff J hn hcard hconj hdiv g z hz hc hnonsplit u).mp
        (hu ▸ c.val.property))
    refine ⟨⟨u,huN⟩,?_⟩
    exact Subtype.ext (Subtype.ext hu)
  have hCc : Nat.card C=q^3+1 := by
    rw [←Nat.card_congr (Equiv.ofBijective j ⟨hjinj,hjsurj⟩)]
    dsimp only [N]
    rw [rootsOfUnity_eq_ker,IsCyclic.card_powMonoidHom_ker,Nat.card_units,hE]
    apply Nat.gcd_eq_right
    have he : (q^3)^2-1=(q^3-1)*(q^3+1) := by
      simpa only [one_pow,mul_comm] using Nat.sq_sub_sq (q^3) 1
    rw [he]; exact dvd_mul_left _ _
  let δ : C →* normOne J :=
    { toFun := fun c => ⟨GeneralLinearGroup.det c.val.val,
        eq_inv_of_mul_eq_one_left (Theory.SpecificGroups.SU3.BinaryPRegularClasses.det_norm J c.val)⟩
      map_one' := Subtype.ext (map_one GeneralLinearGroup.det)
      map_mul' := fun c e => Subtype.ext (map_mul GeneralLinearGroup.det c.val.val e.val.val) }
  let D := (Subgroup.centralizer ({g.val}:Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype
  let k : D →* δ.ker :=
    { toFun := fun b =>
        ⟨⟨⟨b.val.val,b.val.property.1⟩,b.property⟩,Subtype.ext b.val.property.2⟩
      map_one' := Subtype.ext (Subtype.ext (Subtype.ext rfl))
      map_mul' := fun b c => Subtype.ext (Subtype.ext (Subtype.ext rfl)) }
  have hkinj : Function.Injective k := by
    intro b c h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : δ.ker => x.val.val.val) h
  have hksurj : Function.Surjective k := by
    intro b
    have hb : GeneralLinearGroup.det b.val.val.val=1 := congrArg Subtype.val b.property
    refine ⟨⟨⟨b.val.val.val,⟨b.val.val.property,hb⟩⟩,b.val.property⟩,?_⟩
    rfl
  have hkc : Nat.card δ.ker=q^2-q+1 := by
    rw [←Nat.card_congr (Equiv.ofBijective k ⟨hkinj,hksurj⟩)]
    exact (centralizer J hn hcard hconj hdiv g z hz hc hnonsplit).2
  have hδcard : Nat.card δ.range=Nat.card (normOne J) := by
    have he := δ.ker.card_mul_index
    rw [Subgroup.index_ker,hkc,hCc] at he
    rw [normOne_card J hcard hconj]
    have hf : (q^2-q+1)*(q+1)=q^3+1 := by
      have hh := Nat.sub_add_cancel (show q≤q^2 by nlinarith)
      nlinarith
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0<q^2-q+1) (he.trans hf.symm)
  have hsurj : Function.Surjective δ := MonoidHom.range_eq_top.mp
    (eq_top_of_card_eq δ.range hδcard)
  let d' : normOne J := ⟨d,eq_inv_of_mul_eq_one_left hd⟩
  obtain ⟨c,hc'⟩ := hsurj d'
  exact ⟨c.val,mem_centralizer_singleton_iff.mp c.property,congrArg Subtype.val hc'⟩

/-- Same nonsplit scalar cube gives conjugacy by a determinant-one unitary matrix. -/
theorem special_conjugate_of_same_cube [Finite F] {p n : ℕ} [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (hn : 0<n)
    (hcard : Nat.card F=(p^n)^2) (hconj : ∀ x, J.conj x=x^(p^n))
    (hdiv : 3 ∣ p^n+1) (g h : J.unitarySubgroup)
    (z : Fˣ) (hz : J.conj (z:F)*z=1)
    (hg : g.val.val^3=Matrix.scalar (Fin 3) (z:F))
    (hh : h.val.val^3=Matrix.scalar (Fin 3) (z:F))
    (hnonsplit : ∀ a : F, a^3≠(z:F)) :
    ∃ P : J.specialSubgroup, P.val*g.val*P.val⁻¹=h.val := by
  obtain ⟨Q,hQ⟩ := unitary_conjugate_of_same_cube J hn hcard hconj hdiv g h z hz hg hh hnonsplit
  have hd : J.conj (↑((GeneralLinearGroup.det Q.val)⁻¹) : F)*↑((GeneralLinearGroup.det Q.val)⁻¹)=1 := by
    simp only [Units.val_inv_eq_inv_val,map_inv₀,←mul_inv,GeneralLinearGroup.val_det_apply]
    rw [Theory.SpecificGroups.SU3.BinaryPRegularClasses.det_norm J Q,inv_one]
  obtain ⟨c,hcg,hcd⟩ := exists_unitary_commuting_det J hn hcard hconj hdiv g z hz hg hnonsplit
    (GeneralLinearGroup.det Q.val)⁻¹ hd
  have hdet : GeneralLinearGroup.det (Q.val*c.val)=1 := by rw [map_mul,hcd,mul_inv_cancel]
  refine ⟨⟨Q.val*c.val,⟨J.unitarySubgroup.mul_mem Q.property c.property,hdet⟩⟩,?_⟩
  change (Q.val*c.val)*g.val*(Q.val*c.val)⁻¹=h.val
  calc
    _ = Q.val*(c.val*g.val*c.val⁻¹)*Q.val⁻¹ := by group
    _ = Q.val*g.val*Q.val⁻¹ := by rw [hcg.eq]; group
    _ = h.val := hQ
end Matrix.UnitarySinger

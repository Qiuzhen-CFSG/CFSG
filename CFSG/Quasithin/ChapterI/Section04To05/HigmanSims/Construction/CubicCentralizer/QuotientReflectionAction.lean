module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.MarkedSix
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.CubicReflectionAction
public import Theory.GroupTheory.NormalizerQuotientInner
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner

/-!
# The original endpoint reflection on its actual S3 quotient image

The same reflection acts on the literal image of the normalizer cubic
centralizer. Trivial action would let a cubic displacement adjustment lift
every quotient element into its order-two fixed subgroup, contradicting the
image's order six. The nontrivial involutory action is inner by an actual
involution of that image.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem cubic_displacement_fixed (t r x : G) (ht3 : t^3=1)
    (hinv : r*t*r⁻¹=t⁻¹) (hd : (r*x*r⁻¹)/x ∈ zpowers t) :
    let d := (r*x*r⁻¹)/x
    r*(d^2*x)*r⁻¹ = d^2*x := by
  let a := MulAut.conj r
  let d := (r*x*r⁻¹)/x
  have hdt : d ∈ zpowers t := hd
  obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hdt
  have hd3 : d^3=1 := by
    rw [←hn,←zpow_natCast,←zpow_mul,Int.mul_comm,zpow_mul]
    simp only [zpow_natCast,ht3,one_zpow]
  have had : a d=d⁻¹ := by
    rw [←hn,map_zpow]
    change (r*t*r⁻¹)^n=(t^n)⁻¹
    rw [hinv,inv_zpow]
  have hax : a x=d*x := by simp only [a,d,MulAut.conj_apply,div_mul_cancel]
  have hdi : d⁻¹=d^2 := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_succ] using hd3)
  change a (d^2*x)=d^2*x
  rw [map_mul,map_pow,had,hax]
  calc
    (d⁻¹)^2*(d*x)=d⁻¹*x := by group
    _=d^2*x := by rw [hdi]

private theorem involutive_inner_of_symmetric_three {H : Type*} [Group H]
    (e : H ≃* Equiv.Perm (Fin 3)) (a : MulAut H) (ha2 : a^2=1) (hane : a≠1) :
    ∃ k : H, orderOf k=2 ∧ a=MulAut.conj k := by
  let b := (MulAut.congr e) a
  obtain ⟨s,hs⟩ := NormalSymmetricThreePairRank.symmetricThree_aut_inner b
  have heq : a=MulAut.conj (e.symm s) := by
    apply (MulAut.congr e).injective
    change b = (MulAut.congr e) (MulAut.conj (e.symm s))
    rw [hs]
    ext x
    simp [MulAut.congr_apply,MulAut.conj_apply]
  have hk1 : e.symm s≠1 := by
    intro hh
    apply hane
    rw [heq,hh,map_one]
  have hk2 : (e.symm s)^2=1 := by
    have hc : MulAut.conj ((e.symm s)^2)=1 := by rw [map_pow,←heq,ha2]
    apply e.injective
    rw [map_one]
    apply NormalSymmetricThreePairRank.symmetricThree_center_trivial
    intro y
    have hh := DFunLike.congr_fun hc (e.symm y)
    change (e.symm s)^2 * e.symm y * ((e.symm s)^2)⁻¹ = e.symm y at hh
    have hcomm := congrArg e (mul_inv_eq_iff_eq_mul.mp hh)
    simpa only [map_mul,e.apply_symm_apply,map_one] using hcomm.symm
  exact ⟨e.symm s,orderOf_eq_prime hk2 hk1,heq⟩

/-- The original endpoint reflection induces a nontrivial inner involution
on the literal S3 image of its full normalizer cubic centralizer. Both the
ambient quotient action and its restriction retain their evaluation maps. -/
theorem TypeAt.cubic_quotient_reflection_inner (h : TypeAt z V)
    {A : Subgroup G} [IsElementaryAbelian 2 A] (d : NaturalEndpointData A)
    (t r : G) (htz : t∈involutionCentralizer z) (ht : t∈d.carrier)
    (ht3 : orderOf t=3) (hzN : z∈normalizer (A : Set G))
    (hr : r∈d.carrier) (hr2 : orderOf r=2) (hinv : r*t*r⁻¹=t⁻¹) :
    let C := centralizer ({t} : Set G)
    let O := pPrimeCore 2 C
    let X := C⧸O
    let q := QuotientGroup.mk' O
    let E := normalizer (A : Set G)⊓C
    let H := (E.subgroupOf C).map q
    ∃ hrC : r∈normalizer (C : Set G),
      let α := normalizerQuotientAction C O ⟨r,hrC⟩
      ∃ β : MulAut H, β≠1 ∧ β^2=1 ∧
        (∀ x : H, (β x : X)=α (x : X)) ∧
        (∀ x : C, α (q x)=q (C.normalizerMonoidHom ⟨r,hrC⟩ x)) ∧
        ∃ k : H, orderOf k=2 ∧ β=MulAut.conj k := by
  classical
  let C := centralizer ({t} : Set G)
  let O := pPrimeCore 2 C
  let X := C⧸O
  let q := QuotientGroup.mk' O
  let E := normalizer (A : Set G)⊓C
  let D := E.subgroupOf C
  let H := D.map q
  obtain ⟨_,_,_,_,hH6,_,⟨eH⟩,_⟩ := h.cubic_quotient_marked_six d t htz ht ht3 hzN
  obtain ⟨hrE,hfix2,_⟩ := d.cubic_reflection_action t r ht ht3 hr hr2 hinv
  have hrC : r∈normalizer (C : Set G) := by
    have hh : r∈normalizer (zpowers t : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [MonoidHom.map_zpowers]
      change zpowers (r*t*r⁻¹)=zpowers t
      rw [hinv,zpowers_inv]
    simpa only [zpowers_eq_closure,centralizer_closure] using
      normalizer_le_normalizer_centralizer (zpowers t) hh
  let α := normalizerQuotientAction C O ⟨r,hrC⟩
  have hαq (x : C) : α (q x)=q (C.normalizerMonoidHom ⟨r,hrC⟩ x) :=
    quotientAut_apply_mk O (C.normalizerMonoidHom ⟨r,hrC⟩) x
  have hrSq : r^2=1 := by simpa only [hr2] using pow_orderOf_eq_one r
  have hα2 : α^2=1 := by
    change (normalizerQuotientAction C O ⟨r,hrC⟩)^2=1
    rw [←map_pow]
    have hh : (⟨r,hrC⟩ : normalizer (C : Set G))^2=1 := Subtype.ext hrSq
    rw [hh,map_one]
  have hαinv (x : X) : α (α x)=x := by
    have hh := DFunLike.congr_fun hα2 x
    exact hh
  have hαH (x : X) (hx : x∈H) : α x∈H := by
    obtain ⟨y,hy,rfl⟩ := hx
    rw [hαq]
    apply mem_map_of_mem
    change r*(y : G)*r⁻¹∈E
    exact (mem_normalizer_iff.mp hrE y).mp hy
  let β : MulAut H := {
    toFun x := ⟨α x,hαH x x.property⟩
    invFun x := ⟨α x,hαH x x.property⟩
    left_inv x := Subtype.ext (hαinv x)
    right_inv x := Subtype.ext (hαinv x)
    map_mul' x y := Subtype.ext (α.map_mul x y) }
  have hβ2 : β^2=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change α (α (x : X))=(x : X)
    exact hαinv x
  have hO : O.map C.subtype=zpowers t := h.cubic_centralizer_oddCore t htz ht3
  have hβne : β≠1 := by
    intro hb
    let F := E⊓centralizer ({r} : Set G)
    let f : F →* H := (q.comp (inclusion (show F≤C from inf_le_left.trans inf_le_right))).codRestrict H
      (fun x => mem_map_of_mem q (show (⟨x,x.property.1.2⟩ : C)∈D from x.property.1))
    have hfs : Function.Surjective f := by
      intro y
      obtain ⟨x,hx,hxy⟩ := y.property
      have hqfix : α (q x)=q x := by
        have hh := congrArg (fun a : H => (a : X)) (DFunLike.congr_fun hb (⟨q x,mem_map_of_mem q hx⟩ : H))
        exact hh
      let x' := C.normalizerMonoidHom ⟨r,hrC⟩ x
      have hδO : x'/x∈O := by
        apply QuotientGroup.eq_iff_div_mem.mp
        change q x'=q x
        exact (hαq x).symm.trans hqfix
      let δ : G := (r*(x : G)*r⁻¹)/(x : G)
      have hδT : δ∈zpowers t := hO ▸ mem_map_of_mem C.subtype hδO
      have htE : t∈E := ⟨d.normalizes ht,mem_centralizer_singleton_iff.mpr rfl⟩
      have hδE : δ∈E := zpowers_le.mpr htE hδT
      have hfixed := cubic_displacement_fixed t r (x : G)
        (by simpa only [ht3] using pow_orderOf_eq_one t) hinv hδT
      have hδq : q (⟨δ,hδE.2⟩ : C)=1 := by
        exact (QuotientGroup.eq_one_iff (x'/x)).mpr hδO
      have haE : δ^2*(x : G)∈E := E.mul_mem (E.pow_mem hδE 2) hx
      have haF : δ^2*(x : G)∈F := ⟨haE,mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp hfixed).symm⟩
      refine ⟨⟨δ^2*(x : G),haF⟩,?_⟩
      apply Subtype.ext
      change q ((⟨δ,hδE.2⟩ : C)^2*x)=(y : X)
      rw [map_mul,map_pow,hδq,one_pow,one_mul]
      exact hxy
    have hh := Nat.card_le_card_of_surjective f hfs
    rw [hH6,hfix2] at hh
    omega
  refine ⟨hrC,β,hβne,hβ2,fun _ => rfl,hαq,?_⟩
  exact involutive_inner_of_symmetric_three eH β hβ2 hβne

end CFSG.Quasithin.HigmanSims

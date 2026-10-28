module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.TransvectionLift
public import Theory.GroupTheory.QuaternionReflectionCosetClasses
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.FixedProduct
public import Theory.SpecificGroups.SL2.ThreeResidualCore
/-!
# Outside central-square classes in the quaternion central product

For the full orthogonal action on a normal quaternion central product, the
factor-sign kernel cuts the selected Sylow subgroup in index two. A corrected
transvection lift centralizes one actual SL2(3) residual factor. The two outside
central-square classes are represented by that lift and its product with an
order-four element of this factor. When the second representative is an
involution, it fixes a noncentral involution of the original quaternion core.

The proof removes the second quaternion coordinate by an outer coboundary,
fuses the first order-four coordinate inside SL2(3), and uses a quaternion
partner in each factor to construct the fixed involution.

Source: Aschbacher--Smith, (2.4.29), printed p.546.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup.QuaternionCentralProductData
variable {G : Type*} [Group G] [Finite G]

private theorem quaternion_square_mem_intersection
    (B C : Subgroup G) (hB : Nonempty (B≃*QuaternionGroup 2))
    (hi : Nat.card (B⊓C:Subgroup G)=2)
    (hc : ∀b∈B,∀c∈C,b*c=c*b) (a : B) : (a:G)^2∈B⊓C := by
  rw [intersection_eq_factor_center B C hB hi hc]
  refine ⟨a^2,mem_center_iff.mpr ?_,rfl⟩
  intro x
  apply hB.some.injective
  simp only [map_mul,map_pow]
  exact (by decide +kernel : ∀a x:QuaternionGroup 2,x*a^2=a^2*x) _ _

theorem outside_square_classes_and_fixed_involution
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcent : centralizer (Q:Set G)≤Q)
    (k : QuaternionResidualCentralProduct Q d)
    (T : Sylow 2 G) (S : Subgroup G)
    (hf : Function.Surjective
      (d.quotientWreathAction.comp (MulAut.conjNormal : G→*MulAut Q)))
    (hS : S=(T:Subgroup G)⊓(BinaryFourPlus.factorSign.comp
      (d.quotientWreathAction.comp (MulAut.conjNormal : G→*MulAut Q))).ker)
    (z : G) (hz : z∈(center Q).map Q.subtype) (hz1 : z≠1) :
    ∃ y a:G, ∃L:Subgroup G,
      y∈(T:Subgroup G) ∧ y∉S ∧ y^2∈(center Q).map Q.subtype ∧
      a∈Q ∧ orderOf a=4 ∧ a^2=z ∧ Commute y a ∧
      IsPPerfect 2 L ∧ z∈L.pCoreIn 2 ∧ y∈centralizer (L:Set G) ∧
      (∀t∈(T:Subgroup G), t∉S → t^2∈(center Q).map Q.subtype →
        IsConj t y ∨ IsConj t (y*a)) ∧
      (orderOf (y*a)=2 → ∃b∈Q, orderOf b=2 ∧
        b∉centralizer (Q:Set G) ∧ (y*a)*b=b*(y*a)) := by
  obtain ⟨y,hy,hyout,hy2,hya,htrans,hcover⟩ :=
    d.exists_sylow_transvection_with_conjugacy Q hcent k T S hf hS
  obtain ⟨B,C,L,hB,hC,hspan,hinter,hcard,hcomm,hBL,hBcore,hL,hyL,α,hα,ho,happly⟩ :=
    d.residual_transvection_orientation Q k y hya htrans
  have hzI : z∈B⊓C := hinter ▸ hz
  have hBQ : B≤Q := hspan ▸ le_sup_left
  have hCQ : C≤Q := hspan ▸ le_sup_right
  let aB : B := hB.some.symm (QuaternionGroup.a 1)
  have ha4 : orderOf (aB:G)=4 :=
    (orderOf_injective B.subtype B.subtype_injective aB).trans
      ((hB.some.symm.orderOf_eq _).trans QuaternionGroup.orderOf_a_one)
  have haI : (aB:G)^2∈B⊓C := quaternion_square_mem_intersection B C hB hcard hcomm aB
  have ha2ne : (aB:G)^2≠1 := by
    intro hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [ha4] at hd
    norm_num at hd
  have ha2 : (aB:G)^2=z := by
    obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1:(B⊓C:Subgroup G))).mp hcard
    have hh := (hw ⟨(aB:G)^2,haI⟩ (fun hh=>ha2ne (congrArg Subtype.val hh))).trans
      (hw ⟨z,hzI⟩ (fun hh=>hz1 (congrArg Subtype.val hh))).symm
    exact congrArg Subtype.val hh
  have hay : Commute y (aB:G) := (hyL aB (hBL aB.property)).symm
  have hp : IsPPerfect 2 L :=
    GLS3.Chapter5.SchurPresentation.sl23_twoPerfect.of_surjective
      hL.some.symm.toMonoidHom hL.some.symm.surjective
  have hzcore : z∈L.pCoreIn 2 := by
    change z∈(pCore 2 L).map L.subtype
    rw [←hBcore]
    exact hzI.1
  refine ⟨y,aB,L,hy,hyout,hy2,hBQ aB.property,ha4,ha2,hay,hp,hzcore,hyL,?_,?_⟩
  · intro t ht htout ht2
    obtain ⟨m,hm⟩ := hcover t ht htout ht2
    let r := m*t*m⁻¹
    have hr : r∈(Q:Set G)*({y}:Set G) :=
      ⟨r*y⁻¹,hm,y,by simp,by dsimp [r]; group⟩
    have hr2 : r^2∈(center Q).map Q.subtype := by
      obtain ⟨q,hq,hqeq⟩ := ht2
      have hn : m*t^2*m⁻¹=t^2 := by
        rw [←hqeq]
        exact congrArg Subtype.val (d.fixes_center (MulAut.conjNormal m) ⟨q,hq⟩)
      rw [show r^2=m*t^2*m⁻¹ by dsimp [r]; simp only [pow_two]; group,hn]
      exact ⟨q,hq,hqeq⟩
    have hcl := quaternion_reflection_coset_classes B C L hB hC hcard hcomm hBL hL.some
      y hyL (hinter ▸ hy2) α hα ho happly z hzI hz1 aB aB.property ha4 r
      (by simpa only [hspan] using hr) (hinter ▸ hr2)
    have htr : IsConj t r := isConj_iff.mpr ⟨m,rfl⟩
    rcases hcl with hh|hh
    · exact Or.inl (htr.trans hh)
    · exact Or.inr (by simpa only [hay.eq] using htr.trans hh)
  · intro hv2
    have hvpow : (y*(aB:G))^2=1 := by
      simpa only [hv2] using pow_orderOf_eq_one (y*(aB:G))
    have hzsq : z^2=1 := by
      have hh := pow_card_eq_one' (x := (⟨z,hzI⟩ : (B⊓C:Subgroup G)))
      rw [hcard] at hh
      exact congrArg Subtype.val hh
    have hmul : y^2*z=1 := by rw [←ha2,←hay.mul_pow]; exact hvpow
    have hyz : y^2=z := by
      calc
        y^2=y^2*(z*z) := by rw [←pow_two,hzsq,mul_one]
        _=(y^2*z)*z := (mul_assoc _ _ _).symm
        _=z := by rw [hmul,one_mul]
    have hyB : y∈centralizer (B:Set G) := centralizer_le hBL hyL
    obtain ⟨b,hb,c,hc,_hb2,_hc2,hm2,hnon,hfix,_⟩ :=
      quaternion_reflection_fixed_product B C hB hC hcard hcomm
        y z aB hyB hyz hzI hz1 aB.property ha4 ha2 α hα ho happly
    have hbQ : b*c∈Q := Q.mul_mem (hCQ hb) (hBQ hc)
    have hn : b*c∉centralizer (Q:Set G) := by simpa only [hspan] using hnon
    have hbne : b*c≠1 := fun hh=>hn (hh ▸ one_mem _)
    exact ⟨b*c,hbQ,orderOf_eq_prime hm2 hbne,hn,hfix⟩
end Subgroup.QuaternionCentralProductData

module
public import Theory.GroupTheory.Recognition.QuasithinM23.CubicFusion
public import Theory.GroupTheory.Recognition.QuasithinM23.CentralInvolution
public import Theory.Representation.BinaryAlternatingSevenCubicRecognition
public import Theory.GroupTheory.CoprimeSubgroupCentralizer
public import Theory.ElementaryAbelian.EightQuotientRank
/-!
# Cubic centralizers in the exceptional binary local geometry

A cubic fixing a nonzero vector in a faithful binary A₇ four-space fixes
exactly four vectors, by the cubic normal form. In PSL₃(2), a cubic has
precisely its cyclic subgroup as centralizer. Lifting through an elementary
two-kernel with four fixed elements therefore gives a centralizer of order
twelve whose squares lie in the original cyclic cubic subgroup.

The two calculations are consumed together by the original exceptional-local
application of Aschbacher–Smith 5.2.15, printed pp.654–655
(`refs/quasithin.pdf`). They require no splitting of the extension.
-/
public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace Theory.GroupTheory.QuasithinM23
private abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
private def cubic : SL := ⟨!![0,1,0;1,1,0;0,0,1], by decide⟩
private theorem cubic_order : orderOf cubic = 3 :=
  orderOf_eq_prime (by decide : cubic^3=1) (by decide : cubic ≠ 1)
private theorem cubic_cent : ∀ x : SL, x * cubic = cubic * x → x = 1 ∨ x = cubic ∨ x = cubic^2 := by
  decide +kernel
theorem psl3Two_cubic_centralizer {x : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)} (hx : orderOf x = 3) :
    centralizer ({x} : Set _) = zpowers x := by
  let e := Matrix.PSL3Two.equiv
  obtain ⟨g,hg⟩ := isConj_iff.mp (psl3Two_cubics_isConj (e cubic) x
    ((e.orderOf_eq cubic).trans cubic_order) hx)
  let a := e.trans (MulAut.conj g)
  have ha : a cubic = x := hg
  apply le_antisymm
  · intro y hy
    have hc : a.symm y * cubic = cubic * a.symm y := by
      apply a.injective
      simpa only [map_mul,MulEquiv.apply_symm_apply,ha] using
        (mem_centralizer_singleton_iff.mp hy)
    rcases cubic_cent (a.symm y) hc with h | h | h
    · have hh := congrArg a h
      have hy1 : y = 1 := by simpa only [MulEquiv.apply_symm_apply,map_one] using hh
      exact hy1 ▸ one_mem _
    · have hh : y = x := by simpa only [MulEquiv.apply_symm_apply,ha] using congrArg a h
      exact hh ▸ mem_zpowers x
    · have hh : y = x^2 := by simpa only [MulEquiv.apply_symm_apply,map_pow,ha] using congrArg a h
      exact hh ▸ pow_mem (mem_zpowers x) 2
  · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
private theorem fixed_cubic_card
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (t : Module.End (ZMod 2) V) (hd : Module.finrank (ZMod 2) V = 4)
    (ht : t^3=1) (hne : t ≠ 1) (hfix : ∃ v, v ≠ 0 ∧ t v = v) :
    Nat.card {v : V // t v = v} = 4 := by
  obtain ⟨b,hb⟩ := BinaryFourCubic.exists_basis_fixedPlaneMatrix hd t ht hne hfix
  let e : {v : V // t v = v} ≃
      {v : Fin 4 → ZMod 2 // BinaryFourCubic.fixedPlaneMatrix.mulVec v = v} :=
    Equiv.subtypeEquiv b.equivFun.toEquiv (by
      intro v
      change t v = v ↔ BinaryFourCubic.fixedPlaneMatrix.mulVec (b.repr v) = b.repr v
      rw [←hb,LinearMap.toMatrix_mulVec_repr]
      exact b.equivFun.injective.eq_iff.symm)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card]
  decide +kernel

/-- A cubic fixing a nonidentity core element fixes exactly four core elements. -/
theorem exceptional_cubic_core_centralizer_card
    {X : Type*} [Group X] [Finite X]
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16)
    (q : X →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = U) (hC : centralizer (U : Set X) = U)
    (c : X) (hc : orderOf c = 3)
    (z : X) (hz : z ∈ U) (hz1 : z ≠ 1) (hcz : Commute c z) :
    Nat.card (U ⊓ centralizer ({c} : Set X) : Subgroup X) = 4 := by
  let ρ := NormalElementaryQuotient.representation U q hq (hk.trans hC.symm)
  have hf := NormalElementaryQuotient.representation_injective U q hq (hk.trans hC.symm)
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ Module.finrank (ZMod 2) (Additive U) = Nat.card (Additive U) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      _ = 2^4 := (Nat.card_congr Additive.toMul).trans hU
  have hqc : q c ≠ 1 := by
    intro hh
    have hdvd := orderOf_dvd_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) c (hk ▸ (show c ∈ q.ker from hh)))
    rw [hc] at hdvd
    norm_num at hdvd
  have ht : ρ (q c)^3=1 := by
    have hp : c^3=1 := hc ▸ pow_orderOf_eq_one c
    rw [←map_pow,←map_pow,hp,map_one,map_one]
  have htne : ρ (q c) ≠ 1 := fun he => hqc (hf (he.trans (map_one _).symm))
  have hfix : ∃ v : Additive U, v ≠ 0 ∧ ρ (q c) v = v := by
    refine ⟨Additive.ofMul ⟨z,hz⟩,fun he => hz1 (congrArg (fun v : Additive U => (v.toMul : X)) he),?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    change c*z*c⁻¹ = z
    rw [hcz.eq,mul_inv_cancel_right]
  have hh := fixed_cubic_card (ρ (q c)) hd ht htne hfix
  let e : {v : Additive U // ρ (q c) v = v} ≃
      (U ⊓ centralizer ({c} : Set X) : Subgroup X) :=
    { toFun := fun v => ⟨v.val.toMul,v.val.toMul.property,mem_centralizer_singleton_iff.mpr (by
        have he := congrArg (fun w : Additive U => (w.toMul : X)) v.property
        rw [NormalElementaryQuotient.representation_apply] at he
        exact (mul_inv_eq_iff_eq_mul.mp he).symm)⟩
      invFun := fun v => ⟨Additive.ofMul ⟨v,v.property.1⟩,by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [NormalElementaryQuotient.representation_apply]
        change c*(v : X)*c⁻¹ = v
        rw [←mem_centralizer_singleton_iff.mp v.property.2,mul_inv_cancel_right]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).symm.trans hh
private theorem centralizer_of_elementary_kernel
    {X Y : Type*} [Group X] [Group Y] [Finite X]
    (U : Subgroup X) [IsElementaryAbelian 2 U]
    (q : X →* Y) (hk : q.ker = U)
    (c : X) (hc : orderOf c = 3)
    (hcent : centralizer ({q c} : Set Y) = zpowers (q c))
    (hfix : Nat.card (U ⊓ centralizer ({c} : Set X) : Subgroup X) = 4) :
    Nat.card (centralizer ({c} : Set X)) = 12 ∧
      ∀ x ∈ centralizer ({c} : Set X), x^2 ∈ zpowers c := by
  let E := U ⊓ centralizer ({c} : Set X)
  let C := centralizer ({c} : Set X)
  have hZ : zpowers c ≤ C := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hUC : ∀ u : E, ∀ a : zpowers c, Commute (u : X) (a : X) := by
    intro u a
    obtain ⟨k,hk⟩ := a.property
    rw [←hk]
    exact (show Commute (u : X) c from mem_centralizer_singleton_iff.mp u.property.2).zpow_right k
  let f : E × zpowers c →* C :=
    { toFun := fun a => ⟨a.1 * a.2,C.mul_mem a.1.property.2 (hZ a.2.property)⟩
      map_one' := Subtype.ext (one_mul _)
      map_mul' := fun a b => Subtype.ext (by
        change ((a.1 : X)*(b.1 : X))*((a.2 : X)*(b.2 : X)) =
          ((a.1 : X)*(a.2 : X))*((b.1 : X)*(b.2 : X))
        rw [mul_assoc,mul_assoc,←mul_assoc (b.1 : X),
          (hUC b.1 a.2).eq,mul_assoc]) }
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [eq_bot_iff_forall]
    rintro ⟨u,a⟩ h
    have he : (u : X)*(a : X) = 1 := congrArg Subtype.val (show f (u,a)=1 from h)
    have hu2 : (u : X)^2=1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ u.property.1
    have ha3 : (a : X)^3=1 := by
      have hd := orderOf_dvd_of_mem_zpowers a.property
      rw [hc] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have ha2 : (a : X)^2=1 := by
      rw [eq_inv_of_mul_eq_one_right he,inv_pow,hu2,inv_one]
    have ha1 : (a : X)=1 := by
      have hh := ha3
      rw [pow_succ,ha2,one_mul] at hh
      exact hh
    change (u,a) = (1,1)
    apply Prod.ext
    · apply Subtype.ext
      change (u : X) = 1
      simpa only [ha1,mul_one] using he
    · apply Subtype.ext
      exact ha1
  have hs : Function.Surjective f := by
    intro x
    have hx : q x ∈ zpowers (q c) := hcent ▸ mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul] using congrArg q (mem_centralizer_singleton_iff.mp x.property))
    obtain ⟨k,hk'⟩ := hx
    let u : X := (x : X)*c^(-k)
    have hu : u ∈ U := by
      rw [←hk,MonoidHom.mem_ker]
      change q ((x : X)*c^(-k)) = 1
      rw [map_mul,map_zpow,←hk',←zpow_add,add_neg_cancel,zpow_zero]
    have huC : u ∈ C := C.mul_mem x.property (hZ (zpow_mem (mem_zpowers c) _))
    refine ⟨(⟨u,hu,huC⟩,⟨c^k,zpow_mem (mem_zpowers c) _⟩),Subtype.ext ?_⟩
    change ((x : X)*c^(-k))*c^k=x
    rw [mul_assoc,←zpow_add,neg_add_cancel,zpow_zero,mul_one]
  constructor
  · rw [←Nat.card_congr (MulEquiv.ofBijective f ⟨hi,hs⟩).toEquiv,Nat.card_prod,hfix,Nat.card_zpowers,hc]
  · intro x hx
    obtain ⟨⟨u,a⟩,h⟩ := hs ⟨x,hx⟩
    have he : (u : X)*(a : X)=x := congrArg Subtype.val h
    rw [←he,(hUC u a).mul_pow,elemPow_eq_one_of_isElementaryAbelian (p := 2) _ u.property.1,one_mul]
    exact pow_mem a.property 2

/-- The actual cubic centralizer in a binary elementary extension of PSL₃(2). -/
theorem elementary_psl3Two_cubic_centralizer
    {X : Type*} [Group X] [Finite X]
    (U : Subgroup X) [IsElementaryAbelian 2 U]
    (q : X →* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) (hk : q.ker = U)
    (c : X) (hc : orderOf c = 3)
    (hfix : Nat.card (U ⊓ centralizer ({c} : Set X) : Subgroup X) = 4) :
    Nat.card (centralizer ({c} : Set X)) = 12 ∧
      ∀ x ∈ centralizer ({c} : Set X), x^2 ∈ zpowers c := by
  have hqc : orderOf (q c) = 3 := by
    apply orderOf_eq_prime
    · simpa only [map_pow,map_one,hc] using congrArg q (pow_orderOf_eq_one c)
    · intro hz
      have hd := orderOf_dvd_of_pow_eq_one
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) c (hk ▸ (show c ∈ q.ker from hz)))
      rw [hc] at hd
      norm_num at hd
  exact centralizer_of_elementary_kernel U q hk c hc (psl3Two_cubic_centralizer hqc) hfix
end Theory.GroupTheory.QuasithinM23


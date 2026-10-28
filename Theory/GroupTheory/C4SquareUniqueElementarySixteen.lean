module
public import Theory.GroupAction.C4SquareCThreeCentralizer
public import Theory.ElementaryAbelian.Basic

/-!
# Uniqueness of an elementary sixteen under a C4-square cubic action

Let R be a normal C₄×C₄ subgroup of a finite group Q and C an elementary
subgroup of order sixteen, with R∩C of order four and Q=RC. Suppose R is
self-centralizing and an automorphism of R of order three commutes with
all conjugation automorphisms from Q. Then every elementary subgroup escaping C has order at most eight.
In particular, C is the unique elementary subgroup of order sixteen when
|C|=16; the bound itself does not require that cardinality. The actual conjugation action is retained;
no abstract order-sixty-four classification or uniqueness premise is used.

The intersection R∩C is every square-one element of R. Write an involution
x outside C as r c. Then r is primitive and c sends r to its inverse.
Comparing c's action with inversion gives a commuting automorphism fixing
that primitive point, so the C₄-square fixed-point theorem makes the two
actions equal. Thus every involution outside C inverts R. If an elementary
subgroup X escapes C, its elements inside C centralize such an x and hence
fix a primitive residual element; their action on R is trivial. The whole
X-image on R then has order at most two, and its kernel lies in R∩C of
order four. Thus |X|≤8, excluding any second elementary subgroup of order16.

This proves the uniqueness step in Stellmacher (10.1)(a3), printed p.61,
with the surrounding C₄-square and cubic-action hypotheses made explicit.
The stronger escaping-subgroup bound also supports the following odd-action
kernel argument in the same source paragraph;
source: `refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup
open scoped commutatorElement

public theorem card_le_eight_of_elementary_not_le_of_c4_square_cubic_action
    {Q : Type*} [Group Q] [Finite Q]
    (R C : Subgroup Q) [R.Normal] [IsElementaryAbelian 2 C]
    (model : Nonempty (R ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (hZcard : Nat.card (R ⊓ C : Subgroup Q) = 4)
    (hcover : R ⊔ C = ⊤) (hself : centralizer (R : Set Q) = R)
    (a : MulAut R) (ha3 : a^3=1) (hane : a≠1)
    (hact : ∀ q : Q, Commute (MulAut.conjNormal q : MulAut R) a)
    (X : Subgroup Q) [IsElementaryAbelian 2 X] (hnot : ¬ X ≤ C) :
    Nat.card X ≤ 8 := by
  classical
  obtain ⟨equiv⟩ := model
  let _ : CommGroup R := equiv.toMonoidHom.commGroupOfInjective equiv.injective
  let Z := R ⊓ C
  let square : R →* R := powMonoidHom 2
  have hZker : Z.subgroupOf R ≤ square.ker := by
    intro z hz
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=C) z hz.2
  have hkerCard : Nat.card square.ker ≤ 4 := by
    let f : square.ker → {v : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // v^2=1} :=
      fun x => ⟨equiv x,by rw [← map_pow]; exact (congrArg equiv x.property).trans equiv.map_one⟩
    have hfinj : Function.Injective f := by
      intro x y hh
      exact Subtype.ext (equiv.injective (congrArg Subtype.val hh))
    have hcard : Nat.card {v : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // v^2=1} = 4 := by
      rw [Nat.card_eq_fintype_card]
      decide
    exact hcard ▸ Nat.card_le_card_of_injective f hfinj
  have hZkerEq : Z.subgroupOf R = square.ker := by
    apply eq_of_le_of_card_ge hZker
    rw [Nat.card_congr (subgroupOfEquivOfLe (show Z ≤ R from inf_le_left)).toEquiv,hZcard]
    exact hkerCard
  have hfull (r : R) (hr : r^2=1) : (r:Q) ∈ Z := by
    have hh : r ∈ square.ker := hr
    rwa [← hZkerEq] at hh
  let action : Q →* MulAut R := MulAut.conjNormal
  have hker : action.ker = R := by
    apply Eq.trans (b:=centralizer (R : Set Q)) ?_ hself
    ext q
    rw [MonoidHom.mem_ker,mem_centralizer_iff]
    constructor
    · intro h r hr
      have hh := congrArg (fun f : MulAut R => (f ⟨r,hr⟩:Q)) h
      change q*r*q⁻¹=r at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro h
      ext r
      change q*(r:Q)*q⁻¹=(r:Q)
      rw [← h r r.property,mul_inv_cancel_right]
  have fixed_primitive (q : Q) (r : R) (hr : r^2≠1)
      (hfix : action q r=r) : q∈R := by
    rw [← hker]
    apply MonoidHom.mem_ker.mpr
    by_contra hne
    exact hr (c4_square_fixed_point_square_eq_one_of_commuting_three ⟨equiv⟩
      a ha3 hane (action q) hne (hact q) r hfix)
  let inversion : MulAut R := {
    toEquiv := Equiv.inv R
    map_mul' := by
      intro x y
      change (x*y)⁻¹=x⁻¹*y⁻¹
      rw [mul_inv_rev,mul_comm] }
  have hinv (r : R) : inversion r=r⁻¹ := rfl
  have hinvcomm : Commute inversion a := by
    apply MulEquiv.ext
    intro r
    change (a r)⁻¹=a r⁻¹
    exact (map_inv a r).symm
  have inverse_primitive (q : Q) (r : R) (hr : r^2≠1)
      (hinverse : action q r=r⁻¹) : action q=inversion := by
    let c := inversion * action q
    have hcfix : c r=r := by
      change (action q r)⁻¹=r
      rw [hinverse,inv_inv]
    have hccomm : Commute c a := hinvcomm.mul_left (hact q)
    have hcone : c=1 := by
      by_contra hne
      exact hr (c4_square_fixed_point_square_eq_one_of_commuting_three ⟨equiv⟩
        a ha3 hane c hne hccomm r hcfix)
    apply MulEquiv.ext
    intro s
    have hh := congrArg (fun f : MulAut R => f s) hcone
    change (action q s)⁻¹=s at hh
    change action q s=s⁻¹
    simpa only [inv_inv] using congrArg Inv.inv hh
  have outside (x : Q) (hx2 : x^2=1) (hxC : x∉C) :
      ∃ (r : Q) (hr : r∈R), ∃ c∈C, r*c=x ∧ (⟨r,hr⟩:R)^2≠1 ∧ action x=inversion := by
    have hx : x∈R⊔C := hcover ▸ mem_top x
    obtain ⟨r,hr,c,hc,hprod⟩ := mem_sup_of_normal_left.mp hx
    have hr2 : (⟨r,hr⟩:R)^2≠1 := by
      intro hr2
      have hrC : r∈C := (hfull ⟨r,hr⟩ hr2).2
      exact hxC (hprod ▸ C.mul_mem hrC hc)
    have hc2 : c*c=1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=C) c hc
    have hcInv : c⁻¹=c := inv_eq_of_mul_eq_one_left hc2
    have hxi : (r*c)*(r*c)=1 := by rw [hprod,← pow_two,hx2]
    have hcr : c*r*c⁻¹=r⁻¹ := by
      rw [hcInv]
      have hh : r*(c*r*c)=1 := by simpa only [mul_assoc] using hxi
      exact eq_inv_of_mul_eq_one_right hh
    have hactInv : action c=inversion := inverse_primitive c ⟨r,hr⟩ hr2 (Subtype.ext hcr)
    have hactr : action r=1 := MonoidHom.mem_ker.mp (hker.ge hr)
    refine ⟨r,hr,c,hc,hprod,hr2,?_⟩
    rw [← hprod,map_mul,hactr,one_mul,hactInv]
  obtain ⟨x,hx,hxC⟩ := SetLike.not_le_iff_exists.mp hnot
  have hx2 := elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=X) x hx
  obtain ⟨r,hr,c,hc,hprod,hr2,hxinv⟩ := outside x hx2 hxC
  have inside (y : Q) (hy : y∈X) (hyC : y∈C) : action y=1 := by
    have hyx : y*x=x*y := setLike_mul_comm (s:=X) hy hx
    have hyc : y*c=c*y := setLike_mul_comm (s:=C) hyC hc
    have hyr : y*r=r*y := by
      rw [← hprod] at hyx
      apply mul_right_cancel (b:=c)
      calc
        y*r*c = y*(r*c) := mul_assoc _ _ _
        _ = (r*c)*y := hyx
        _ = r*(c*y) := mul_assoc _ _ _
        _ = r*(y*c) := by rw [hyc]
        _ = r*y*c := (mul_assoc _ _ _).symm
    have hyR := fixed_primitive y ⟨r,hr⟩ hr2 (Subtype.ext (by
      change y*r*y⁻¹=r
      rw [hyr,mul_inv_cancel_right]))
    exact MonoidHom.mem_ker.mp (hker.ge hyR)
  let f : X →* MulAut R := action.comp X.subtype
  have hRimage : f.range ≤ zpowers inversion := by
    rintro _ ⟨y,rfl⟩
    change action (y:Q) ∈ zpowers inversion
    by_cases hyC : (y:Q)∈C
    · rw [inside y y.property hyC]
      exact (zpowers inversion).one_mem
    · obtain ⟨_,_,_,_,_,_,hyi⟩ := outside y
        (elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=X) y y.property) hyC
      rw [hyi]
      exact mem_zpowers inversion
  have hpowInv : inversion^2=1 := by
    apply MulEquiv.ext
    intro r
    change (r⁻¹)⁻¹=r
    exact inv_inv r
  have hRcard : Nat.card f.range ≤ 2 := by
    apply (card_le_of_le hRimage).trans
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide : 0<2) (orderOf_dvd_of_pow_eq_one hpowInv)
  let kernelToZ : f.ker → Z := fun y =>
    ⟨((y:X):Q),hfull ⟨((y:X):Q),by
      exact hker.le y.property⟩ (Subtype.ext
        (elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=X) y y.val.property))⟩
  have hkinj : Function.Injective kernelToZ := by
    intro y z hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : Z => (t:Q)) hh
  have hKcard : Nat.card f.ker ≤ 4 := by
    have hh := Nat.card_le_card_of_injective kernelToZ hkinj
    exact hZcard ▸ hh
  have hcount := f.ker.card_mul_index
  rw [index_ker] at hcount
  calc
    Nat.card X = Nat.card f.ker * Nat.card f.range := hcount.symm
    _ ≤ 4 * 2 := Nat.mul_le_mul hKcard hRcard
    _ = 8 := by decide


public theorem unique_elementary_sixteen_of_c4_square_cubic_action
    {Q : Type*} [Group Q] [Finite Q]
    (R C : Subgroup Q) [R.Normal] [IsElementaryAbelian 2 C]
    (model : Nonempty (R ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (hCcard : Nat.card C = 16) (hZcard : Nat.card (R ⊓ C : Subgroup Q) = 4)
    (hcover : R ⊔ C = ⊤) (hself : centralizer (R : Set Q) = R)
    (a : MulAut R) (ha3 : a^3=1) (hane : a≠1)
    (hact : ∀ q : Q, Commute (MulAut.conjNormal q : MulAut R) a)
    (X : Subgroup Q) [IsElementaryAbelian 2 X] (hXcard : Nat.card X = 16) :
    X = C := by
  by_cases hle : X ≤ C
  · exact eq_of_le_of_card_ge hle (by omega)
  · have hh := card_le_eight_of_elementary_not_le_of_c4_square_cubic_action
      R C model hZcard hcover hself a ha3 hane hact X hle
    omega

end Subgroup

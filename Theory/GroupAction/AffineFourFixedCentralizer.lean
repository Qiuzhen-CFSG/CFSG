module
public import Theory.GroupAction.FourPointFixedOrbit
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A centralizer of index prime to three on an affine four-point coset

Let K normalize an abelian subgroup O and its order-four subgroup Z, and
suppose [O,K] lies in Z. For t in K and a t-fixed point d in D≤O outside Z,
assume that the Z-points centralizing t lie in D. Then a nonidentity point
y in D has centralizer of index prime to three inside K.

The literal conjugation action restricts to the fiber of d in O/Z, a set
of four points. The fixed-orbit theorem supplies a t-fixed point whose K-orbit
has order prime to three. Its ratio with d belongs to Z and centralizes t,
so the point belongs to D; the nontrivial quotient coset excludes identity.
The actual point stabilizer is the native centralizer restricted to K.

This source-neutral affine transfer is used in Stellmacher (10.1)(16),
printed p.64, with O the neighborhood omega center and Z the middle center.
No faithful action, acting-group order, chosen odd subgroup, or orbit-size
assumption is introduced.
-/

open scoped IsMulCommutative commutatorElement
universe u
namespace Subgroup

public theorem exists_fixed_centralizer_three_coprime_index_on_four_coset
    {G : Type u} [Group G] [Finite G]
    (K O Z D : Subgroup G) [IsMulCommutative O]
    (hKO : K ≤ normalizer (O : Set G)) (_hKZ : K ≤ normalizer (Z : Set G))
    (hZO : Z ≤ O) (hZcard : Nat.card Z = 4) (hcomm : ⁅O,K⁆ ≤ Z)
    (hDO : D ≤ O) (t : K) (d : G) (hd : d ∈ D) (hdZ : d ∉ Z)
    (htd : (t:G)*d=d*(t:G))
    (hfixed : Z ⊓ centralizer ({(t:G)} : Set G) ≤ D) :
    ∃ y : G, y ∈ D ∧ y ≠ 1 ∧ Nat.Coprime 3 ((centralizer ({y} : Set G)).relIndex K) := by
  classical
  let _ := conjMulDistribMulActionOfLeNormalizer K O hKO
  let N := Z.subgroupOf O
  let q : O →* O ⧸ N := QuotientGroup.mk' N
  let dO : O := ⟨d,hDO hd⟩
  have hqsmul (k : K) (x : O) : q (k • x) = q x := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (k:G)*(x:G)*(k:G)⁻¹/(x:G) ∈ Z
    simpa only [commutatorElement_def,div_eq_mul_inv] using
      (hcomm (Subgroup.commutator_comm K O ▸
        (Subgroup.commutator_mem_commutator k.property x.property)))
  let X : SubMulAction K O := {
    carrier := {x | q x = q dO}
    smul_mem' := fun k _ hx => (hqsmul k _).trans hx }
  let f : N → X := fun n => ⟨dO*(n:O),by
    change q (dO*(n:O)) = q dO
    rw [map_mul,show q (n:O)=1 from (QuotientGroup.eq_one_iff _).mpr n.property,mul_one]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y heq
      apply Subtype.ext
      exact mul_left_cancel (congrArg (fun x : X => (x:O)) heq)
    · intro x
      have hn : dO⁻¹*(x:O) ∈ N := by
        have hh := QuotientGroup.eq_iff_div_mem.mp x.property
        simpa only [div_eq_mul_inv,mul_comm] using hh
      refine ⟨⟨dO⁻¹*(x:O),hn⟩,?_⟩
      apply Subtype.ext
      change dO*(dO⁻¹*(x:O))=(x:O)
      simp only [mul_inv_cancel_left]
  have hXcard : Nat.card X = 4 := by
    rw [← Nat.card_congr (Equiv.ofBijective f hf)]
    exact (Nat.card_congr (subgroupOfEquivOfLe hZO).toEquiv).trans hZcard
  let x : X := ⟨dO,rfl⟩
  have htx : t • x = x := by
    apply Subtype.ext
    apply Subtype.ext
    change (t:G)*d*(t:G)⁻¹=d
    exact mul_inv_eq_iff_eq_mul.mpr htd
  obtain ⟨y,hty,hcop⟩ := MulAction.exists_fixed_point_three_coprime_orbit_of_card_four hXcard t x htx
  let point : G := ((y:O):G)
  have hratio : point/d ∈ Z := by
    have hh : (y:O)/dO ∈ N := QuotientGroup.eq_iff_div_mem.mp y.property
    exact hh
  have htpoint : (t:G)*point=point*(t:G) := by
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun y : X => ((y:O):G)) hty)
  have hratiofixed : point/d ∈ centralizer ({(t:G)} : Set G) :=
    (centralizer ({(t:G)} : Set G)).div_mem
      (mem_centralizer_singleton_iff.mpr htpoint.symm)
      (mem_centralizer_singleton_iff.mpr htd.symm)
  have hpointD : point ∈ D := by
    have hh := D.mul_mem (hfixed ⟨hratio,hratiofixed⟩) hd
    simpa only [div_mul_cancel] using hh
  have hpointne : point ≠ 1 := by
    intro heq
    apply hdZ
    have hh : d⁻¹ ∈ Z := by simpa only [heq,one_div] using hratio
    simpa only [inv_inv] using Z.inv_mem hh
  have hstab : MulAction.stabilizer K y = (centralizer ({point} : Set G)).subgroupOf K := by
    ext k
    change k • y = y ↔ (k:G) ∈ centralizer ({point} : Set G)
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hh
      exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun y : X => ((y:O):G)) hh)
    · intro hh
      apply Subtype.ext
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr hh
  have hindex : (centralizer ({point} : Set G)).relIndex K =
      Nat.card (MulAction.orbit K y) := by
    rw [Subgroup.relIndex,←hstab,MulAction.index_stabilizer,Nat.card_coe_set_eq]
  refine ⟨point,hpointD,hpointne,?_⟩
  rw [hindex]
  exact hcop

end Subgroup

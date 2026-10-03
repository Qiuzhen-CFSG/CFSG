module
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.Lemmas
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic

/-!
# The cubic orbit of an elementary eight spans an elementary sixteen

Let t be a fixed-point-free automorphism of cube one of a finite group R.
Suppose Z is a t-invariant central subgroup of order four contained in an
elementary abelian subgroup U of order eight, and [U,t(U)] lies in Z.
Then the literal subgroup W=U∨t(U) is elementary abelian of order sixteen
and is t-invariant. R itself need not be a two-group. The supplied
subgroups and automorphism are retained throughout the conclusion.

On any invariant finite subgroup, the displacement map z↦t(z)z⁻¹ is
bijective because t is fixed-point-free. Consequently every coset fixed
modulo that subgroup is trivial. For x∈U, centrality of the three orbit
commutators makes x*t(x)*t²(x) fixed modulo Z, hence an element of Z.
Its square is one, forcing x and t(x) to commute. Since Z has index two
in U, this single-pair calculation makes U and t(U) centralize each other.
Their join is elementary, and the same norm identity gives t-invariance.
The subgroup product formula leaves intersection orders four and eight;
the latter makes U invariant, contradicting the fixed-point congruence
|U|≡1 modulo three. The join therefore has order sixteen.

This source-independent class-two calculation supplies the native W in
Stellmacher (8.6)(b3), Journal of Algebra 190 (1997), printed p.44. The
native caller constructs R, U, Z and their fixed-free cubic action; the
later permutation-module and nonsolvability arguments are separate results.
-/

namespace MulAut
open Subgroup
open scoped IsMulCommutative commutatorElement

private theorem mem_of_fixed_modulo {R : Type*} [Group R] [Finite R]
    (Z : Subgroup R) (t : MulAut R) (hZt : Z.map t.toMonoidHom = Z)
    (hfixed : ∀ r, t r = r → r = 1) (x : R) (hx : t x*x⁻¹ ∈ Z) : x ∈ Z := by
  have hmap (z:R) (hz:z∈Z) : t z∈Z := by
    rw [←hZt]
    exact mem_map_of_mem t.toMonoidHom hz
  let d : Z → Z := fun z => ⟨t z*(z:R)⁻¹,
    Z.mul_mem (hmap z z.property) (Z.inv_mem z.property)⟩
  have hinj : Function.Injective d := by
    intro z w heq
    have hh : t z*(z:R)⁻¹ = t w*(w:R)⁻¹ := congrArg Subtype.val heq
    have hf : t ((w:R)⁻¹*z) = (w:R)⁻¹*z := by
      rw [map_mul,map_inv]
      calc
        (t (w:R))⁻¹*t z = (t (w:R))⁻¹*(t z*(z:R)⁻¹)*z := by group
        _ = (t (w:R))⁻¹*(t w*(w:R)⁻¹)*z := by rw [hh]
        _ = (w:R)⁻¹*z := by group
    exact Subtype.ext (inv_mul_eq_one.mp (hfixed ((w:R)⁻¹*z) hf)).symm
  obtain ⟨z,hz⟩ := Finite.surjective_of_injective hinj ⟨t x*x⁻¹,hx⟩
  have hh : t z*(z:R)⁻¹ = t x*x⁻¹ := congrArg Subtype.val hz
  have htx : t x = t z*(z:R)⁻¹*x := by rw [hh]; group
  have hf : t ((z:R)⁻¹*x) = (z:R)⁻¹*x := by rw [map_mul,map_inv,htx]; group
  have heq : (z:R) = x := inv_mul_eq_one.mp (hfixed _ hf)
  exact heq ▸ z.property

private theorem invariant_card_mod_three {R : Type*} [Group R] [Finite R]
    (H : Subgroup R) (t : MulAut R) (hHt : H.map t.toMonoidHom = H)
    (hthree : t^3=1) (hfixed : ∀ r, t r = r → r = 1) : Nat.card H % 3 = 1 := by
  let a : MulAut H := (t.subgroupMap H).trans (MulEquiv.subgroupCongr hHt)
  have ha (x:H) : (a x:R) = t x := rfl
  have hacube : a^3=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    have hh := congrArg (fun f:MulAut R => f (x:R)) hthree
    change t (t (t (x:R))) = (x:R) at hh
    exact hh
  let _ : IsElementaryAbelian 3 (zpowers a) := IsElementaryAbelian.zpowers_of_pow_eq_one hacube
  have hp := (IsElementaryAbelian.isPGroup 3 (zpowers a)).card_modEq_card_fixedPoints H
  have hbot : FixedPoints.subgroup (zpowers a) H = ⊥ := by
    apply bot_unique
    intro x hx
    have hh := hx ⟨a,mem_zpowers a⟩
    have hf : t (x:R) = (x:R) := congrArg Subtype.val hh
    exact Subtype.ext (hfixed _ hf)
  change Nat.card H % 3 = Nat.card (FixedPoints.subgroup (zpowers a) H) % 3 at hp
  simpa [hbot] using hp

private theorem cubic_norm_and_commute {R : Type*} [Group R] [Finite R]
    (Z : Subgroup R) (t : MulAut R) (hZt : Z.map t.toMonoidHom = Z)
    (hZcenter : Z ≤ center R) (hZsquare : ∀ z∈Z,z^2=1)
    (hthree : t^3=1) (hfixed : ∀ r, t r = r → r = 1)
    (x : R) (hx2:x^2=1) (hxy:⁅x,t x⁆ ∈ Z) :
    x*t x*t (t x) ∈ Z ∧ Commute x (t x) := by
  have ht3 (r:R) : t (t (t r)) = r := by
    have hh := congrArg (fun f:MulAut R => f r) hthree
    exact hh
  have hZX (z:R) (hz:z∈Z) : t z ∈ Z := hZt ▸ mem_map_of_mem t.toMonoidHom hz
  have hzx : ⁅t (t x),x⁆ ∈ Z := by
    have hh := hZX _ (hZX _ hxy)
    simpa only [map_commutatorElement,ht3] using hh
  have hyx : ⁅t x,x⁆ ∈ Z := by simpa only [commutatorElement_inv] using Z.inv_mem hxy
  have hyzx : ⁅t x*t (t x),x⁆ ∈ Z := by
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hc := mem_center_iff.mp (hZcenter hzx) (t x)
    rw [hc,mul_inv_cancel_right]
    exact Z.mul_mem hzx hyx
  have hnorm : x*t x*t (t x) ∈ Z := by
    apply mem_of_fixed_modulo Z t hZt hfixed
    have heq : t (x*t x*t (t x))*(x*t x*t (t x))⁻¹ = ⁅t x*t (t x),x⁆ := by
      simp only [map_mul,ht3,commutatorElement_def]
      group
    rwa [heq]
  refine ⟨hnorm,?_⟩
  let n := x*t x*t (t x)
  have hn : n^2=1 := hZsquare n hnorm
  have hz : (t (t x))^2=1 := by rw [←map_pow,←map_pow,hx2,map_one,map_one]
  have hnz : Commute n (t (t x))⁻¹ := (mem_center_iff.mp (hZcenter hnorm) _).symm
  have hprod : x*t x = n*(t (t x))⁻¹ := by dsimp [n]; group
  have hprod2 : (x*t x)^2=1 := by rw [hprod,hnz.mul_pow,hn,inv_pow,hz,inv_one,mul_one]
  have hy2 : (t x)^2=1 := by rw [←map_pow,hx2,map_one]
  have hix : x⁻¹=x := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hx2)
  have hiy : (t x)⁻¹=t x := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hy2)
  have hip : (x*t x)⁻¹=x*t x := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hprod2)
  change x*t x=t x*x
  calc
    x*t x = (x*t x)⁻¹ := hip.symm
    _ = t x*x := by rw [mul_inv_rev,hix,hiy]

public theorem elementary_sixteen_of_cubic_orbit_eight
    {R : Type*} [Group R] [Finite R]
    (Z U : Subgroup R) (hZU : Z ≤ U) (hZcenter : Z ≤ center R)
    (hZcard : Nat.card Z = 4) (hUcard : Nat.card U = 8)
    (hU : IsElementaryAbelian 2 U)
    (t : MulAut R) (hthree : t^3=1) (hfixed : ∀ r, t r = r → r = 1)
    (hZt : Z.map t.toMonoidHom = Z)
    (hcomm : ⁅U,U.map t.toMonoidHom⁆ ≤ Z) :
    IsElementaryAbelian 2 (U ⊔ U.map t.toMonoidHom : Subgroup R) ∧
      Nat.card (U ⊔ U.map t.toMonoidHom : Subgroup R) = 16 ∧
      (U ⊔ U.map t.toMonoidHom).map t.toMonoidHom = U ⊔ U.map t.toMonoidHom := by
  classical
  let _ := hU
  let V := U.map t.toMonoidHom
  let W := U ⊔ V
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.map t.toMonoidHom
  have hVs : Nat.card V = 8 := (card_map_of_injective t.injective).trans hUcard
  have hZV : Z ≤ V := by
    rw [←hZt]
    exact map_mono hZU
  have hZsquare (z:R) (hz:z∈Z) : z^2=1 := elemPow_eq_one_of_isElementaryAbelian z (hZU hz)
  have hlocal (x:R) (hx:x∈U) : x*t x*t (t x) ∈ Z ∧ Commute x (t x) :=
    cubic_norm_and_commute Z t hZt hZcenter hZsquare hthree hfixed x
      (elemPow_eq_one_of_isElementaryAbelian x hx)
      (hcomm (commutator_mem_commutator hx (mem_map_of_mem t.toMonoidHom hx)))
  have hindex : Z.relIndex U = 2 := by
    have hh := (Z.subgroupOf U).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv,hZcard,hUcard] at hh
    change 4 * Z.relIndex U = 8 at hh
    omega
  have hnot : ¬ U ≤ Z := by
    intro hUZ
    have hh := Nat.card_congr (MulEquiv.subgroupCongr (le_antisymm hUZ hZU)).toEquiv
    rw [hUcard,hZcard] at hh
    omega
  obtain ⟨u,hu,huZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hcoset (v:R) (hv:v∈U) (hvZ:v∉Z) : u⁻¹*v ∈ Z :=
    (Z.subgroupOf U).mul_mem_iff_of_index_two hindex
      (a := ⟨u⁻¹,U.inv_mem hu⟩) (b := ⟨v,hv⟩) |>.mpr (by
        simp only [mem_subgroupOf,inv_mem_iff,huZ,hvZ])
  have hZmap (z:R) (hz:z∈Z) : t z∈Z := by
    rw [←hZt]
    exact mem_map_of_mem t.toMonoidHom hz
  have hcentral : V ≤ centralizer (U:Set R) := by
    rintro _ ⟨w,hw,rfl⟩
    apply mem_centralizer_iff.mpr
    intro v hv
    change v*t w=t w*v
    by_cases hvZ:v∈Z
    · exact (mem_center_iff.mp (hZcenter hvZ) (t w)).symm
    by_cases hwZ:w∈Z
    · exact mem_center_iff.mp (hZcenter (hZmap w hwZ)) v
    have ha := hcoset v hv hvZ
    have hb := hZmap _ (hcoset w hw hwZ)
    have h1 : Commute u (t (u⁻¹*w)) := mem_center_iff.mp (hZcenter hb) u
    have h2 : Commute (u⁻¹*v) (t u*t (u⁻¹*w)) :=
      (mem_center_iff.mp (hZcenter ha) _).symm
    have hc := ((hlocal u hu).2.mul_right h1).mul_left h2
    simpa only [←map_mul,mul_inv_cancel_left] using hc.eq
  have hWE : IsElementaryAbelian 2 W := IsElementaryAbelian.sup_of_le_centralizer hcentral
  have hthird (x:R) (hx:x∈U) : t (t x)∈W := by
    have heq : t (t x)=(x*t x)⁻¹*(x*t x*t (t x)) := by group
    rw [heq]
    exact W.mul_mem
      (W.inv_mem (W.mul_mem ((show U≤W from le_sup_left) hx)
        ((show V≤W from le_sup_right) (mem_map_of_mem t.toMonoidHom hx))))
      ((show U≤W from le_sup_left) (hZU (hlocal x hx).1))
  have hWle : W.map t.toMonoidHom ≤ W := by
    rw [Subgroup.map_sup]
    refine sup_le le_sup_right ?_
    rintro _ ⟨y,⟨x,hx,rfl⟩,rfl⟩
    exact hthird x hx
  have hWt : W.map t.toMonoidHom = W := eq_of_le_of_card_ge hWle
    (by rw [card_map_of_injective t.injective])
  let I := U ⊓ V
  have hZI : Z ≤ I := le_inf hZU hZV
  have hIlo : 4 ≤ Nat.card I := by
    rw [←hZcard]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hZI) (Subgroup.inclusion_injective hZI)
  have hIdiv : Nat.card I ∣ 2^3 := by
    change Nat.card I ∣ 8
    simpa only [hUcard] using card_dvd_of_le (show I≤U from inf_le_left)
  obtain ⟨n,hn,hIn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hIdiv
  have hIcases : Nat.card I=4 ∨ Nat.card I=8 := by
    interval_cases n
    · change Nat.card I=1 at hIn
      omega
    · change Nat.card I=2 at hIn
      omega
    · exact Or.inl hIn
    · exact Or.inr hIn
  have hIcard : Nat.card I=4 := by
    rcases hIcases with h | h
    · exact h
    have hIU : I=U := eq_of_le_of_card_ge inf_le_left (by rw [h,hUcard])
    have hUV : U≤V := hIU ▸ inf_le_right
    have hVU : V=U := (eq_of_le_of_card_ge hUV (by rw [hVs,hUcard])).symm
    have hmod := invariant_card_mod_three U t hVU hthree hfixed
    norm_num [hUcard] at hmod
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes U V
    (le_normalizer_iff_commutator_le_left.mpr (hcomm.trans hZU))
  change Nat.card U * Nat.card V = Nat.card I * Nat.card W at hprod
  rw [hUcard,hVs,hIcard] at hprod
  exact ⟨hWE,by change Nat.card W=16; omega,hWt⟩

end MulAut

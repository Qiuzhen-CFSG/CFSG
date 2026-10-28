module

public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel
public import Theory.GroupTheory.QuaternionCentralProductFactors
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Cubic decomposition in the actual quaternion-action quotient

Let U be a normal central product of two quaternion eights and Q the kernel
of H's action on U/Z(U). Suppose the image K* of O²(H) is elementary of order
nine. An involution swapping the factors cannot invert all of K*: otherwise
restriction to either factor plane would be faithful, embedding a group of
order nine into the six-element automorphism group of a Klein four-group.
Cubic actions preserve the factors because their cubes are inner and their
squares preserve the intrinsic quaternion factors.

A non-inverted element x gives the nonidentity fixed cubic x*xᵃ. Its cyclic
subgroup is disjoint from the marked inverted cubic R*. Counting inside K*
then gives the literal equality K* = C_{K*}(a*) R*. The containment R* ≤ K*
is derived from odd element orders and preservation of the two-residual by
the actual quotient map. This works with an arbitrary action kernel Q, hence
in particular Q = O₂(H), without a self-centralizing hypothesis on U.

The factor calculations adapt the local arguments in ActionDichotomy.CubicInversion;
this independent leaf permits the normalizer-product assembly to import it.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the swapping
alternative in the proof of Lemma 14.4.4, printed p.1007. This supplies the
quotient coverage premise of normalizer_product_of_centralizer_control;
the lifting and earlier-source centralizer controls remain with that theorem.
-/
open Subgroup
open scoped Pointwise

namespace Subgroup.QuaternionCentralProductData.QuotientCalculation

private theorem not_inverts_of_swaps
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    (σ : G →* MulAut V) (hσ : Function.Injective σ)
    (B C : Subgroup V) (hspan : B ⊔ C = ⊤)
    (hB : Nat.card (MulAut B) < 9)
    (A : Subgroup G) (hA : Nat.card A = 9)
    (hpres : ∀ x ∈ A, B.map (σ x).toMonoidHom = B)
    (a : G) (hswap : B.map (σ a).toMonoidHom = C) :
    ∃ x ∈ A, a*x*a⁻¹ ≠ x⁻¹ := by
  classical
  by_contra! hi
  let f : A →* MulAut B := {
    toFun x := ((σ x).subgroupMap B).trans (MulEquiv.subgroupCongr (hpres x x.property))
    map_one' := by ext v; exact DFunLike.congr_fun σ.map_one (v : V)
    map_mul' x y := by ext v; exact DFunLike.congr_fun (σ.map_mul x y) (v : V) }
  have hf (x : A) (v : B) : (f x v : V) = σ x v := rfl
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have hfixB : ∀ v ∈ B, σ x v = v := by
      intro v hv
      exact congrArg Subtype.val (DFunLike.congr_fun hx (⟨v,hv⟩ : B))
    have hrel : σ a * σ x = (σ x)⁻¹ * σ a := by
      have hh := congrArg σ (hi x x.property)
      rw [map_mul,map_mul,map_inv,map_inv] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hfixC : ∀ v ∈ C, σ x v = v := by
      rw [← hswap]
      rintro _ ⟨v,hv,rfl⟩
      have hh := DFunLike.congr_fun hrel v
      simp only [MulAut.mul_apply,hfixB v hv] at hh
      have hh' := congrArg (σ x) hh
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.apply_inv_self] using hh'
    have hall : ⊤ ≤ (σ x).toMonoidHom.eqLocus (MonoidHom.id V) :=
      hspan ▸ sup_le hfixB hfixC
    have he : σ x = 1 := MulEquiv.ext (fun v => hall (mem_top v))
    exact Subtype.ext (hσ (he.trans σ.map_one.symm))
  have hcard := Nat.card_le_card_of_injective f hinj
  omega

private theorem nine_product
    {G : Type*} [Group G] [Finite G]
    (A R : Subgroup G) [A.Normal] [R.Normal] [IsElementaryAbelian 3 A]
    (hA : Nat.card A = 9) (hR : Nat.card R = 3) (hRA : R ≤ A)
    (a : G) (ha : a^2=1)
    (hi : ∀ r ∈ R, a*r*a⁻¹=r⁻¹)
    (hn : ∃ x ∈ A, a*x*a⁻¹ ≠ x⁻¹) :
    (A : Set G) = ((A ⊓ centralizer {a} : Subgroup G) : Set G) * (R : Set G) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm (x y : G) (hx : x ∈ A) (hy : y ∈ A) : x*y=y*x :=
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x,hx⟩ : A) ⟨y,hy⟩)
  obtain ⟨x,hx,hxn⟩ := hn
  let y := a*x*a⁻¹
  have hy : y ∈ A := Normal.conj_mem inferInstance x hx a
  let c := x*y
  have hc : c ∈ A := A.mul_mem hx hy
  have hcc : c ∈ centralizer {a} := by
    apply mem_centralizer_singleton_iff.mpr
    have hai : a⁻¹=a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha)
    change c*a=a*c
    calc
      c*a = x*(a*x*a⁻¹)*a := rfl
      _ = x*a*x := by group
      _ = a*((a*x*a⁻¹)*x) := by
        have haa : a*a=1 := by simpa only [pow_two] using ha
        rw [hai]
        simp only [← mul_assoc,haa,one_mul]
      _ = a*c := congrArg (a * ·) (hcomm x y hx hy).symm
  have hcne : c ≠ 1 := by
    intro he
    exact hxn (mul_eq_one_iff_eq_inv'.mp he)
  have hc3 : c^3=1 := elemPow_eq_one_of_isElementaryAbelian c hc
  let D := zpowers c
  have hDA : D ≤ A := zpowers_le.mpr hc
  have hDC : D ≤ centralizer {a} := zpowers_le.mpr hcc
  have hdis : Disjoint R D := by
    apply disjoint_iff_inf_le.mpr
    intro z hz
    change z=1
    have hzfix : a*z*a⁻¹=z := by
      rw [← mem_centralizer_singleton_iff.mp (hDC hz.2), mul_inv_cancel_right]
    have hzi : z=z⁻¹ := hzfix.symm.trans (hi z hz.1)
    have hz2 : z^2=1 := by simpa only [pow_two] using mul_eq_one_iff_eq_inv.mpr hzi
    have hz3 : z^3=1 := elemPow_eq_one_of_isElementaryAbelian z (hRA hz.1)
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz2) (orderOf_dvd_of_pow_eq_one hz3)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hd))
  have hD : Nat.card D = 3 := by rw [Nat.card_zpowers,orderOf_eq_prime hc3 hcne]
  have hjoin : D ⊔ R = A := by
    apply eq_of_le_of_card_ge (sup_le hDA hRA)
    have he := card_sup_eq_mul_of_normalizes_of_disjoint R D
      (by rw [R.normalizer_eq_top]; exact le_top) hdis
    rw [sup_comm,hD,hR] at he
    rw [hA,he]
  apply Set.Subset.antisymm
  · intro z hz
    have hp : z ∈ (D : Set G)*(R : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right D R (by rw [R.normalizer_eq_top]; exact le_top),hjoin]
      exact hz
    obtain ⟨d,hd,r,hr,rfl⟩ := hp
    exact ⟨d,⟨hDA hd,hDC hd⟩,r,hr,rfl⟩
  · rintro _ ⟨c,hc,r,hr,rfl⟩
    exact A.mul_mem hc.1 (hRA hr)
end Subgroup.QuaternionCentralProductData.QuotientCalculation


open Subgroup
namespace Subgroup.QuaternionCentralProductData.QuotientCalculation
variable {V : Type*} [Group V] [Finite V] (d : QuaternionCentralProductData V)

omit [Finite V] in
private theorem factor_normal (B C : Subgroup V)
    (hc : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) (hs : B ⊔ C = ⊤) : B.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hs]
  exact sup_le B.le_normalizer ((show C ≤ centralizer (B : Set V) from
    fun c hc' b hb => hc b hb c hc').trans (centralizer_le_normalizer _))

private theorem cube_trivial_preserves (b : MulAut V)
    (hb : (quotientAut (center V) b)^3=1) :
    d.left.map b.toMonoidHom = d.left ∧ d.right.map b.toMonoidHom = d.right := by
  have hinner : ∃ q : V, MulAut.conj q = b^3 := by
    apply (d.quotientAut_eq_one_iff_inner (b^3)).mp
    rwa [map_pow]
  obtain ⟨q,hq⟩ := hinner
  have hsquare := quaternion_factors_invariant_of_square d.left d.right d.left_model
    d.right_model d.intersection_card d.commute b (by rw [d.span]; exact map_top_of_surjective _ b.surjective)
  have hcube (B C : Subgroup V) (hc : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
      (hs : B ⊔ C = ⊤) : B.map (b^3).toMonoidHom = B := by
    rw [← hq]
    let := factor_normal B C hc hs
    exact Normal.map_conj_eq B q
  have calcmap (B : Subgroup V) (hB : (B.map b.toMonoidHom).map b.toMonoidHom = B)
      (hB3 : B.map (b^3).toMonoidHom = B) : B.map b.toMonoidHom = B := by
    have hm : (b^3).toMonoidHom = b.toMonoidHom.comp (b.toMonoidHom.comp b.toMonoidHom) := by
      ext x
      rfl
    have hc : B.map (b^3).toMonoidHom = B.map b.toMonoidHom := by
      rw [hm, ← map_map, ← map_map, hB]
    exact hc.symm.trans hB3
  constructor
  · exact calcmap d.left hsquare.1 (hcube d.left d.right d.commute d.span)
  · exact calcmap d.right hsquare.2 (hcube d.right d.left (fun c hc b hb => (d.commute b hb c hc).symm)
      (by rw [sup_comm]; exact d.span))

include d in
private theorem factor_image_klein (B : Subgroup V) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hz : center V ≤ B) : IsKleinFour (B.map (QuotientGroup.mk' (center V))) := by
  let E := B.map (QuotientGroup.mk' (center V))
  have hcB : Nat.card B = 8 := by
    rw [Nat.card_congr hB.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hiB : B.index = 4 := by
    have h := B.card_mul_index
    rw [hcB,d.card] at h
    omega
  have hi := B.index_map_eq (QuotientGroup.mk'_surjective (center V))
    (show (QuotientGroup.mk' (center V)).ker ≤ B by rwa [QuotientGroup.ker_mk'])
  have hh := (B.map (QuotientGroup.mk' (center V))).card_mul_index
  rw [hi,hiB,d.quotient_card] at hh
  have hc : Nat.card E = 4 := by dsimp [E]; omega
  let _ := d.quotient_elementary
  let _ : IsElementaryAbelian 2 E := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (V ⧸ center V)) x)) }
  let _ : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩

omit [Finite V] in
private theorem quotient_map_factor (B : Subgroup V) (a : MulAut V) :
    (B.map (QuotientGroup.mk' (center V))).map (quotientAut (center V) a).toMonoidHom =
      (B.map a.toMonoidHom).map (QuotientGroup.mk' (center V)) := by
  rw [map_map, map_map]
  congr 1
  ext x
  exact quotientAut_apply_mk (center V) a x
end Subgroup.QuaternionCentralProductData.QuotientCalculation

namespace Subgroup.QuaternionCentralProductData
open QuotientCalculation
variable {H : Type*} [Group H] [Finite H] (U : Subgroup H) [U.Normal]
    (d : QuaternionCentralProductData U)

/-- The image of the actual two-residual is the product of its centralizer
of the swapping involution and the marked inverted cubic. The order-three
marking itself supplies containment in the residual image. -/
public theorem residual_quotient_cubic_product
    (Q : Subgroup H) [Q.Normal]
    (hker : ((quotientAut (center U)).comp
      (MulAut.conjNormal : H →* MulAut U)).ker = Q)
    (hK : IsElementaryAbelian 3 ((pResidual 2 H).map (QuotientGroup.mk' Q)))
    (hKcard : Nat.card ((pResidual 2 H).map (QuotientGroup.mk' Q)) = 9)
    (R : Subgroup H) (hRn : (R.map (QuotientGroup.mk' Q)).Normal)
    (hRcard : Nat.card (R.map (QuotientGroup.mk' Q)) = 3)
    (a : H) (ha : a^2=1)
    (hswap : d.left.map (MulAut.conjNormal a).toMonoidHom = d.right)
    (hinv : ∀ r ∈ R, QuotientGroup.mk' Q (a*r*a⁻¹) = (QuotientGroup.mk' Q r)⁻¹) :
    ((pResidual 2 H).map (QuotientGroup.mk' Q) : Set (H ⧸ Q)) =
      (((pResidual 2 H).map (QuotientGroup.mk' Q) ⊓
        centralizer {QuotientGroup.mk' Q a} : Subgroup (H ⧸ Q)) : Set (H ⧸ Q)) *
          (R.map (QuotientGroup.mk' Q) : Set (H ⧸ Q)) := by
  let π := QuotientGroup.mk' Q
  let σ₀ := (quotientAut (center U)).comp (MulAut.conjNormal : H →* MulAut U)
  let σ := QuotientGroup.lift Q σ₀ hker.ge
  have hσ : Function.Injective σ := (QuotientGroup.injective_lift_iff _ _ _).mpr hker.symm
  let A := (pResidual 2 H).map π
  let R' := R.map π
  let : IsElementaryAbelian 3 A := hK
  let : A.Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective Q)
  let : R'.Normal := hRn
  let q := QuotientGroup.mk' (center U)
  let B := d.left.map q
  let C := d.right.map q
  have hspan : B ⊔ C = ⊤ := by
    rw [← map_sup,d.span,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  let : IsKleinFour B := factor_image_klein d d.left d.left_model (d.center_eq ▸ inf_le_left)
  have hpres : ∀ x ∈ A, B.map (σ x).toMonoidHom = B := by
    rintro _ ⟨k,hk,rfl⟩
    have hk3 : (π k)^3=1 := elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem π hk)
    have hb : (quotientAut (center U) (MulAut.conjNormal k))^3=1 := by
      have hh := congrArg σ hk3
      simpa only [map_pow, map_one, σ, π, σ₀, QuotientGroup.mk'_apply,
        QuotientGroup.lift_mk, MonoidHom.comp_apply] using hh
    change (d.left.map q).map (quotientAut (center U) (MulAut.conjNormal k)).toMonoidHom = _
    rw [quotient_map_factor, (cube_trivial_preserves d _ hb).1]
  have hswap' : B.map (σ (π a)).toMonoidHom = C := by
    change (d.left.map q).map (quotientAut (center U) (MulAut.conjNormal a)).toMonoidHom = _
    rw [quotient_map_factor,hswap]
  have hn := QuotientCalculation.not_inverts_of_swaps σ hσ B C hspan
    (by rw [IsKleinFour.card_mulAut]; decide) A hKcard hpres (π a) hswap'
  have hRA : R' ≤ A := by
    change R.map π ≤ (pResidual 2 H).map π
    rw [map_pResidual_of_surjective 2 π (QuotientGroup.mk'_surjective Q)]
    intro r hr
    have hr3 : r^3=1 := by
      have hh := pow_card_eq_one' (x := (⟨r,hr⟩ : R'))
      rw [hRcard] at hh
      exact congrArg Subtype.val hh
    exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hr3))
  apply QuotientCalculation.nine_product A R' hKcard hRcard hRA (π a)
    (by rw [← map_pow,ha,map_one]) _ hn
  rintro _ ⟨r,hr,rfl⟩
  simpa only [map_mul,map_inv] using hinv r hr
end Subgroup.QuaternionCentralProductData

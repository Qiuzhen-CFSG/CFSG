module
public import Theory.SpecificGroups.PSL3Two.WreathCubicCentralizer
public import Theory.SpecificGroups.PSL3Two.Automorphisms.SylowStabilizer
public import Theory.GroupTheory.SmallTwoGroupCubicClassification

/-!
# Two-subgroups normalized by cubic planes in the binary wreath square

A two-subgroup of SL₃(2) normalized by a fixed cubic is elementary abelian.
Its order is at most eight; the order-eight case contradicts the
self-normalizing Sylow subgroup. The cubic acts nontrivially because its
centralizer is a three-group. The small cubic-automorphism classification
then excludes the remaining quaternion alternative by its order.

In the base of SL₃(2) wr C₂, apply this calculation to each coordinate.
Sylow conjugacy carries any cubic plane to the two independent standard
cubics. This proves elementarity without choosing a parabolic marking.
The Chapter 10 application uses the literal action of the containing
core on the original module.

Source: the binary parabolic geometry in Aschbacher--Smith I.5.4, printed
p.420, applied to the core comparison in 10.2.5, printed p.748.
The imported matrix models retain their attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two.WreathPair

private def cubic : SL := ⟨!![0,1,0;0,0,1;1,0,0], by decide⟩
private theorem cubic_ne_one : cubic ≠ 1 := by decide +kernel
private theorem cubic_order : orderOf cubic = 3 := by
  exact orderOf_eq_prime (by decide +kernel) cubic_ne_one
private theorem cubic_centralizer_cube : ∀ a : SL, a * cubic = cubic * a → a ^ 3 = 1 := by
  decide +kernel

private theorem coordinate_elementary (U : Subgroup SL) (hU : IsPGroup 2 U)
    (hn : cubic ∈ normalizer (U : Set SL)) : IsElementaryAbelian 2 U := by
  by_cases hbot : U = ⊥
  · subst U
    exact { toIsMulCommutative := inferInstance, exponent_dvd_p := by simp }
  have hcard : Nat.card U ≤ 8 := by
    obtain ⟨S,hS⟩ := hU.exists_le_sylow
    have hh := card_dvd_of_le hS
    have hc : Nat.card S = 8 := by
      rw [S.card_eq_multiplicity,card_SL]
      decide +kernel
    rw [hc] at hh
    exact Nat.le_of_dvd (by decide) hh
  have h8 : Nat.card U ≠ 8 := by
    intro he
    let S : Sylow 2 SL := Sylow.ofCard U (by rw [he,card_SL]; decide +kernel)
    have hc : cubic ∈ (S : Subgroup SL) := (self_normalizing_sylow S) ▸ hn
    have hd := (S : Subgroup SL).orderOf_dvd_natCard hc
    rw [cubic_order,show Nat.card (S : Subgroup SL) = 8 from he] at hd
    norm_num at hd
  let a : MulAut U := U.normalizerMonoidHom ⟨cubic,hn⟩
  have ha3 : a ^ 3 = 1 := by
    rw [←map_pow]
    have he : (⟨cubic,hn⟩ : normalizer (U : Set SL)) ^ 3 = 1 :=
      Subtype.ext (by change cubic ^ 3 = 1; decide +kernel)
    rw [he,map_one]
  have hane : a ≠ 1 := by
    intro he
    apply hbot
    apply bot_unique
    intro u hu
    have hh := congrArg (fun f : MulAut U => (f ⟨u,hu⟩ : SL)) he
    change cubic * u * cubic⁻¹ = u at hh
    have hu3 := cubic_centralizer_cube u (mul_inv_eq_iff_eq_mul.mp hh).symm
    obtain ⟨n,hn⟩ := hU.exists_orderOf_dvd_pow ⟨u,hu⟩
    have hd : orderOf u ∣ 2 ^ n := by simpa only [Subgroup.orderOf_mk] using hn
    exact mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (by exact (show Nat.Coprime 2 3 by decide).pow_left n) hd (orderOf_dvd_of_pow_eq_one hu3)))
  rcases elementary_or_quaternion_of_small_two_group_cubic hU hcard a ha3 hane with he | hquat
  · exact he
  · obtain ⟨e⟩ := hquat
    apply (h8 _).elim
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]
    decide +kernel

private def planeHom : (Bit → zpowers cubic) →* Actor where
  toFun a := ⟨fun i => (a i : SL),1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp

private theorem planeHom_injective : Function.Injective planeHom := by
  intro a b he
  funext i
  exact Subtype.ext (congrArg (fun w : Actor => w.left i) he)

private theorem plane_card : Nat.card planeHom.range = 9 := by
  rw [Nat.card_congr (MonoidHom.ofInjective planeHom_injective).toEquiv.symm,
    Nat.card_fun,Nat.card_zpowers,cubic_order]
  change 3 ^ Nat.card (ZMod 2) = 9
  rw [Nat.card_zmod]
  norm_num

private def planeSylow : Sylow 3 Actor := Sylow.ofCard planeHom.range (by
  rw [plane_card,RegularWreathProduct.card,card_SL]
  change 9 = 3 ^ (168 ^ Nat.card (ZMod 2) * Nat.card (ZMod 2)).factorization 3
  rw [Nat.card_zmod]
  decide +kernel)

private def coordinate (U : Subgroup Actor) (hr : ∀ u ∈ U, u.right = 1) (i : Bit) : U →* SL where
  toFun u := u.val.left i
  map_one' := rfl
  map_mul' u v := by simp [hr u u.property]

private theorem plane_normalized_elementary (U : Subgroup Actor) (hU : IsPGroup 2 U)
    (hr : ∀ u ∈ U, u.right = 1) (hn : planeHom.range ≤ normalizer (U : Set Actor)) :
    IsElementaryAbelian 2 U := by
  classical
  have he (i : Bit) : IsElementaryAbelian 2 (coordinate U hr i).range := by
    apply coordinate_elementary _ (hU.of_surjective _ (coordinate U hr i).rangeRestrict_surjective)
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,⟨u,rfl⟩,rfl⟩
      let a : Actor := planeHom (fun _ => ⟨cubic,mem_zpowers cubic⟩)
      have ha : a ∈ normalizer (U : Set Actor) := hn ⟨_,rfl⟩
      have hmem : a * (u : Actor) * a⁻¹ ∈ U :=
        (mem_normalizer_iff.mp ha u).mp u.property
      refine ⟨⟨_,hmem⟩,?_⟩
      change (a * (u : Actor) * a⁻¹).left i = cubic * (u.val.left i) * cubic⁻¹
      simp [a,planeHom,hr u u.property]
    · rw [card_map_of_injective (MulAut.conj cubic).injective]
  have hp (u : U) : u ^ 2 = 1 := by
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext i
      let : IsElementaryAbelian 2 (coordinate U hr i).range := he i
      have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) (coordinate U hr i u)
        (show coordinate U hr i u ∈ (coordinate U hr i).range from ⟨u,rfl⟩)
      simpa [pow_two,hr u u.property,coordinate] using hh
    · simp [pow_two,hr u u.property]
  exact {
    toIsMulCommutative := ⟨⟨fun u v => Commute.of_orderOf_dvd_two
      (fun w => orderOf_dvd_of_pow_eq_one (hp w)) u v⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

/-- A two-subgroup of the base normalized by a cubic plane is elementary abelian. -/
theorem two_base_normalized_cubic_plane_elementary (P U : Subgroup Actor)
    (hP : Nat.card P = 9) (hU : IsPGroup 2 U)
    (hr : ∀ u ∈ U, u.right = 1) (hn : P ≤ normalizer (U : Set Actor)) :
    IsElementaryAbelian 2 U := by
  let S : Sylow 3 Actor := Sylow.ofCard P (by
    rw [hP,RegularWreathProduct.card,card_SL]
    change 9 = 3 ^ (168 ^ Nat.card (ZMod 2) * Nat.card (ZMod 2)).factorization 3
    rw [Nat.card_zmod]
    decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Actor S planeSylow
  let e := MulAut.conj g
  have he : P.map e.toMonoidHom = planeHom.range := congrArg Sylow.toSubgroup hg
  let U' := U.map e.toMonoidHom
  let : IsElementaryAbelian 2 U' := plane_normalized_elementary U' (hU.map _)
    (by rintro _ ⟨u,hu,rfl⟩; simp [e,MulAut.conj_apply,hr u hu])
    (he ▸ (map_mono hn).trans (le_normalizer_map e.toMonoidHom))
  exact IsElementaryAbelian.of_injective (U.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom
    (U.equivMapOfInjective e.toMonoidHom e.injective).injective

end Matrix.PSL3Two.WreathPair

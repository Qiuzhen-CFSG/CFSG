module
public import Theory.SpecificGroups.SymplecticFour.OddFrattiniSixteen
public import Theory.SpecificGroups.SL2.CentralTwoExtensions

/-!
# Three generators for odd-prime symplectic Sylow subgroups

The actual odd-index plane-pair stabilizer is SL₂(p) wr C₂. Its base Sylow
is cyclic or generalized quaternion, so has at most two Frattini generators.
The swap adds at most one generator. Odd-index placement and the actual
projective map therefore bound the PSp₄(p) Sylow Frattini quotient by eight.

This sharpens the degree-two estimate in `OddFrattiniSixteen` and excludes
a GL₄(2) outer section in the original doubled-natural branch. The cyclic
and quaternion argument also occurs in `G2.OddFrattiniSixteen`.
Source: Aschbacher--Smith 4.4.10--11 and 12.1.9, printed pp.621 and 793.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.OddFrattiniEight
open Subgroup
open CentralCovers.OddPrime.LargeSections.TwoPrimary
open scoped IsMulCommutative MatrixGroups
variable {p : ℕ} [Fact p.Prime]

private theorem cyclic_frattini_le_two {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) [IsCyclic P] : Nat.card (P ⧸ frattini P) ≤ 2 := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let : IsCyclic (P ⧸ frattini P) := isCyclic_of_surjective
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have h := IsElementaryAbelian.exponent_dvd_p 2 (P ⧸ frattini P)
  rw [IsCyclic.exponent_eq_card] at h
  exact Nat.le_of_dvd (by decide) h

private theorem cyclic_index_frattini_le_four {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (A : Subgroup P) [IsCyclic A] (hi : A.index ≤ 2) :
    Nat.card (P ⧸ frattini P) ≤ 4 :=
  (hP.card_frattini_quotient_le_subgroup_index_mul A).trans
    ((Nat.mul_le_mul hi (cyclic_frattini_le_two (hP.to_subgroup A))).trans (by decide))

private theorem quaternion_subgroup_frattini_le_four {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {n : ℕ} (hn : 0 < n)
    (e : P →* QuaternionGroup n) (he : Function.Injective e) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  let : NeZero n := ⟨hn.ne'⟩
  let A := zpowers (QuaternionGroup.a (1 : ZMod (2*n)))
  have hi : A.index = 2 := by
    have h := A.index_mul_card
    rw [Nat.card_zpowers,QuaternionGroup.orderOf_a_one] at h
    have hc : Nat.card (QuaternionGroup n) = 4*n := by
      rw [Nat.card_eq_fintype_card,QuaternionGroup.card]
    rw [hc] at h
    nlinarith
  let B := A.comap e
  let : IsCyclic B := isCyclic_of_injective (e.subgroupComap A)
    (fun x y h => Subtype.ext (he (congrArg Subtype.val h)))
  apply cyclic_index_frattini_le_four hP B
  let : A.Normal := normal_of_index_eq_two hi
  rw [index_comap]
  exact Nat.le_of_dvd (by decide) (hi ▸ A.relIndex_dvd_index_of_normal e.range)

private theorem sl2_frattini_le_four {F : Type*} [Field F] [Finite F]
    (hF : (2 : F) ≠ 0) (S : Sylow 2 SL(2,F)) :
    Nat.card (S ⧸ frattini S) ≤ 4 := by
  rcases Matrix.SpecialLinearGroup.sylow_two_cyclic_or_quaternion hF S with hc | ⟨n,hn,⟨e⟩⟩
  · let := hc
    exact (cyclic_frattini_le_two S.isPGroup').trans (by decide)
  exact quaternion_subgroup_frattini_le_four S.isPGroup' hn e.toMonoidHom e.injective

private theorem odd_index (ho : Odd p) :
    Odd (PlaneGeometry.inclusion (F := ZMod p)).range.index := by
  by_cases hp : 3 < p
  · exact PlaneGeometry.odd_index hp
  have h3 : p = 3 := by
    have hp2 := (Fact.out : p.Prime).two_le
    have hne : p ≠ 2 := by rintro rfl; norm_num at ho
    omega
  subst p
  have hc := (PlaneGeometry.inclusion (F := ZMod 3)).range.index_mul_card
  rw [PlaneGeometry.card_range, card_sp, Nat.card_zmod] at hc
  have hi : (PlaneGeometry.inclusion (F := ZMod 3)).range.index = 45 := by norm_num at hc; omega
  rw [hi]
  decide

/-- Bound on the actual odd-prime symplectic Sylow. -/
theorem frattini_card_le (ho : Odd p) (P : Sylow 2 (Sp (ZMod p))) :
    Nat.card (P ⧸ frattini P) ≤ 8 := by
  let SL := Matrix.SpecialLinearGroup (Fin 2) (ZMod p)
  let WW := BinaryWreathFrattini.W SL
  let : Finite WW := Finite.of_equiv ((SL × SL) × Multiplicative (ZMod 2))
    SemidirectProduct.equivProd.symm
  have hact : BinaryWreathFrattini.action (R := SL) = PlaneGeometry.action := by
    apply MonoidHom.ext
    intro c
    obtain ⟨c,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2)).surjective c
    fin_cases c
    · exact (map_one _).trans (map_one _).symm
    · exact PlaneGeometry.action_generator.symm
  let eW : WW ≃* (SL × SL) ⋊[PlaneGeometry.action] Multiplicative (ZMod 2) :=
    SemidirectProduct.congr (MulEquiv.refl _) (MulEquiv.refl _) (by intro c; rw [hact]; rfl)
  let j : WW →* Sp (ZMod p) := PlaneGeometry.inclusion.comp eW.toMonoidHom
  have hj : Function.Injective j := PlaneGeometry.inclusion_injective.comp eW.injective
  have hjrange : j.range = (PlaneGeometry.inclusion (F := ZMod p)).range :=
    by rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eW.surjective, ←MonoidHom.range_eq_map]
  let R : Sylow 2 SL := default
  let Q : Sylow 2 WW := default
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hp := (Fact.out : p.Prime).two_le
    have hpne : p ≠ 2 := by rintro rfl; norm_num at ho
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
  have hR : Nat.card (R ⧸ frattini R) ≤ 4 := sl2_frattini_le_four htwo R
  have hQ : Nat.card (Q ⧸ frattini Q) ≤ 8 :=
    (BinaryWreathFrattini.sylow_card_frattini_le R Q).trans
      (by have hh := Nat.mul_le_mul_left 2 hR; norm_num at hh ⊢; exact hh)
  let U : Subgroup j.range := (Q : Subgroup WW).map (MonoidHom.ofInjective hj).toMonoidHom
  have hUidx : U.index = (Q : Subgroup WW).index := by
    exact index_map_of_bijective (MonoidHom.ofInjective hj).bijective _
  let Sg : Subgroup (Sp (ZMod p)) := U.map j.range.subtype
  have hSidx : ¬ 2 ∣ Sg.index := by
    rw [index_map_subtype, hUidx]
    rw [hjrange]
    exact Nat.prime_two.not_dvd_mul Q.not_dvd_index (odd_index ho).not_two_dvd_nat
  have hS : IsPGroup 2 Sg := (Q.isPGroup'.map _).map _
  let S : Sylow 2 (Sp (ZMod p)) := hS.toSylow hSidx
  let e₁ : Q ≃* U := Q.equivMapOfInjective (MonoidHom.ofInjective hj).toMonoidHom
    (MonoidHom.ofInjective hj).injective
  let e₂ : U ≃* S := U.equivMapOfInjective j.range.subtype Subtype.val_injective
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv S),
    ←Theory.GroupTheory.SylowFrattiniBounds.card_congr (e₁.trans e₂)]
  exact hQ

/-- Transport through the actual prime field and full projective quotient. -/
theorem projective_frattini_card_le {F : Type*} [Field F] [Finite F]
    (ho : Odd p) (hF : Nat.card F = p)
    (P : Sylow 2 (Sp F ⧸ center (Sp F))) : Nat.card (P ⧸ frattini P) ≤ 8 := by
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F Fact.out
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let a := CentralCovers.OddPrime.fieldEquivPSp e
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (a.subgroupMap (P : Subgroup _))]
  exact OddClassicalSylowFrattini.card_le_of_surjective
    (QuotientGroup.mk' (center (Sp (ZMod p)))) (QuotientGroup.mk'_surjective _)
    (frattini_card_le ho) Q

end Theory.SpecificGroups.SymplecticFour.OddFrattiniEight


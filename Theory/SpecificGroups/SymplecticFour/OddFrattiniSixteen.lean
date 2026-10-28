module
public import Theory.Representation.DegreeTwoFrattini
public import Theory.GroupTheory.BinaryWreathFrattini
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary.PlaneGeometry
public import Theory.SpecificGroups.OddClassicalSylowFrattini

/-!
# The odd-prime symplectic Sylow Frattini bound

The stabilizer of an unordered pair of orthogonal symplectic planes has
odd index in Sp₄(p), including p = 3. It is SL₂(p) wr C₂. The degree-two
bound and the swap relation bound its Sylow Frattini quotient by sixteen.
Surjective descent gives the same bound for the actual projective quotient.

The exterior Hall consumer excludes a PSL₅(2) section in the outer action
on a component with this central quotient, retaining its full central cover.
Source: Aschbacher--Smith 4.4.10--11, printed p.621.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.OddFrattiniSixteen
open Subgroup
open CentralCovers.OddPrime.LargeSections.TwoPrimary
open scoped MatrixGroups
variable {p : ℕ} [Fact p.Prime]

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
    Nat.card (P ⧸ frattini P) ≤ 16 := by
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
  have hR : Nat.card (R ⧸ frattini R) ≤ 8 := by
    let f := Matrix.SpecialLinearGroup.toGL.comp (R : Subgroup SL).subtype
    apply Representation.card_frattini_quotient_le_eight_of_faithful_degree_two R.isPGroup'
      ((Representation.generalLinearNatural 2).comp f)
      ((Representation.generalLinearNatural_injective 2).comp
        (Matrix.SpecialLinearGroup.toGL_injective.comp Subtype.val_injective)) htwo
    simp
  have hQ : Nat.card (Q ⧸ frattini Q) ≤ 16 :=
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
    (P : Sylow 2 (Sp F ⧸ center (Sp F))) : Nat.card (P ⧸ frattini P) ≤ 16 := by
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F Fact.out
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let a := CentralCovers.OddPrime.fieldEquivPSp e
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (a.subgroupMap (P : Subgroup _))]
  exact OddClassicalSylowFrattini.card_le_of_surjective
    (QuotientGroup.mk' (center (Sp (ZMod p)))) (QuotientGroup.mk'_surjective _)
    (frattini_card_le ho) Q

end Theory.SpecificGroups.SymplecticFour.OddFrattiniSixteen


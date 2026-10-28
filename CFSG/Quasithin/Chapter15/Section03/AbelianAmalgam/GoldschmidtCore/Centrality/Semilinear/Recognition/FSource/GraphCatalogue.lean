module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.ThirtyTwo
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.LinearGraphCoverSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.UnitaryGraphCoverSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.WreathedExponent

/-!
# Literal graph row from the component Sylow invariants

The genuine earlier A/C catalogue, an order-32 component-quotient Sylow,
and its exponent-eight and noncommutativity invariants select odd prime
degree three. The actual matrix Sylow shapes produce W32 and hence the
correct sign. The marked central-cover graph theorems construct the outside
involution, ambient generation and original component action. Field and form
transport respect the literal consumer universe and local extension maps.

Source: Aschbacher--Smith F.6.18(11), printed p.310. The residual Sylow
order and power bounds remain the earlier marked order-64 amalgam step;
no component-family, field-sign, cover, or graph-action premise is retained.
-/

public noncomputable section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}

/-- The genuine source catalogue and the residual Sylow invariants construct literal row (11). -/
theorem eleven_of_source_sylow32_exponent_eight
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (generalizedFitting G ⧸ center (generalizedFitting G)))
    (hH : IsSQTK κ H) (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G))
    (hres : pResidual 2 G = generalizedFitting G) (hproper : generalizedFitting G ≠ ⊤)
    (S : Sylow 2 G)
    (P : Sylow 2 (generalizedFitting G ⧸ center (generalizedFitting G)))
    (hP : Nat.card P = 32) (he : ∀ x : P, x ^ 8 = 1) (hnc : ¬ IsMulCommutative P)
    (hsylow : Extension S C4Square E4)
    (hleft : QuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (DihedralGroup 6)) : Alternative G₁ G₂ S := by
  have hm := component_central_quotient_model hA hC hH
    (eG.symm.toMonoidHom.comp (QuotientGroup.mk' _))
    (eG.symm.surjective.comp (QuotientGroup.mk'_surjective _)) hK
  obtain ⟨p, hp, ho, hm⟩ :=
    ComponentSieve.LargeGoldschmidt.theoremC_degree_three_of_sylow32 P hP he hnc hm
  let : Fact p.Prime := ⟨hp⟩
  rcases hm with hm | hm
  · obtain ⟨F, hF, hfin, hc, ⟨j⟩⟩ := hm
    let E := ULift.{u} F
    let a : F ≃+* E := ULift.ringEquiv.symm
    have hE : Nat.card E = p := by simpa [E] using hc
    let eK := j.trans (Atlas.fieldEquivPSL 3 a)
    let Q := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
    let aP : P ≃* Q := (P : Subgroup _).equivMapOfInjective eK.toMonoidHom eK.injective
    have hQ : Nat.card Q = 32 := (Nat.card_congr aP.symm.toEquiv).trans hP
    have heQ : ∀ x : Q, x ^ 8 = 1 := fun x => aP.symm.injective (by
      simpa only [map_pow, map_one] using he (aP.symm x))
    obtain ⟨w⟩ := psl3_wreathed_of_sylow32_exponent_eight hp ho hE Q hQ heQ
    have hs := psl3_sign_of_wreathed_sylow hp ho hE Q w
    exact eleven_linear_of_source_component_quotient eG hK hres hproper S hp ho hE hs
      eK hsylow hleft hright
  · obtain ⟨F, hF, hfin, J, hc, hj, ⟨j⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F p := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)
    let E := ULift.{u} F
    let a : F ≃+* E := ULift.ringEquiv.symm
    let σ : E ≃+* E := a.symm.trans (J.conj.trans a)
    have hσ : Function.Involutive σ := by
      intro x
      change a (J.conj (a.symm (a (J.conj (a.symm x))))) = x
      rw [a.symm_apply_apply, J.conj_involutive, a.apply_symm_apply]
    let J' : HermitianForm 3 E := identityForm σ hσ
    obtain ⟨C, hC⟩ := J.exists_orthonormal_basis_of_prime_frobenius hj hc
    let b := (projectiveBasisEquiv J C hC).trans
      (projectiveCoefficientEquiv a J.conj J.conj_involutive σ hσ (by
        intro x
        change a (J.conj x) = a (J.conj (a.symm (a x)))
        rw [a.symm_apply_apply]))
    have hE : Nat.card E = p ^ 2 := by simpa [E] using hc
    have hJ' : ∀ x, J'.conj x = x ^ p := by
      intro x
      change a (J.conj (a.symm x)) = x ^ p
      rw [hj, map_pow, a.apply_symm_apply]
    let eK := j.trans b
    let Q := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
    let aP : P ≃* Q := (P : Subgroup _).equivMapOfInjective eK.toMonoidHom eK.injective
    have hQ : Nat.card Q = 32 := (Nat.card_congr aP.symm.toEquiv).trans hP
    have heQ : ∀ x : Q, x ^ 8 = 1 := fun x => aP.symm.injective (by
      simpa only [map_pow, map_one] using he (aP.symm x))
    obtain ⟨w⟩ := psu3_wreathed_of_sylow32_exponent_eight J' hp ho hE hJ' Q hQ heQ
    have hs := psu3_sign_of_wreathed_sylow J' hp ho hE hJ' Q w
    have hm := Theory.ClassicalSmallSylow.psu3_mod_eight_of_small_sylow J' hp.one_lt hE hJ'
      Q (by rw [hQ]; decide) hs
    exact eleven_unitary_cover_of_source_component eG hres hproper hK.2 S J' hp hm hE hJ'
      eK hsylow hleft hright

/-- The same consumer when the earlier marked source supplies the full W32 model. -/
theorem eleven_of_wreathed_component_source
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (generalizedFitting G ⧸ center (generalizedFitting G)))
    (hH : IsSQTK κ H) (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G))
    (hres : pResidual 2 G = generalizedFitting G) (hproper : generalizedFitting G ≠ ⊤)
    (S : Sylow 2 G)
    (P : Sylow 2 (generalizedFitting G ⧸ center (generalizedFitting G)))
    (eP : P ≃* W32)
    (hsylow : Extension S C4Square E4)
    (hleft : QuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (DihedralGroup 6)) : Alternative G₁ G₂ S := by
  apply eleven_of_source_sylow32_exponent_eight hA hC hH eG hK hres hproper S P
    ((Nat.card_congr eP.toEquiv).trans wreathedThirtyTwo_card) ?_ ?_ hsylow hleft hright
  · intro x
    exact eP.injective (by simpa only [map_pow, map_one] using wreathedThirtyTwo_pow_eight (eP x))
  · intro hc
    apply wreathedThirtyTwo_not_commutative
    exact isMulCommutative_iff.mpr fun x y => eP.symm.injective (by
      simpa only [map_mul] using (isMulCommutative_iff.mp hc) (eP.symm x) (eP.symm y))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource

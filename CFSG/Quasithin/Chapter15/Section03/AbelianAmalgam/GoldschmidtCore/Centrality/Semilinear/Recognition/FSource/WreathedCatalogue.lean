module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.ThirtyTwo
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.WreathedSource

/-!
# The W32 source catalogue in literal F.6 row (10)

The genuine Chapter C component catalogue and the complete order-32 Sylow
sieve produce an odd prime degree-three model. The wreathed Sylow center
selects the sign, and the source cover theorem determines the possible
central cover. Transporting the field and Hermitian form into the consumer
universe gives the literal row-(10) conclusion with its original local maps.

Source: Aschbacher--Smith F.6.18(10), pp.309--310. The ambient-component
equality and the two marked local extensions remain earlier-source inputs.
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

/-- The full source catalogue gives literal row (10) when its component is the ambient group. -/
theorem ten_of_wreathed_source_component_top
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (generalizedFitting G ⧸ center (generalizedFitting G)))
    (hH : IsSQTK κ H) (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G)) (htop : generalizedFitting G = ⊤)
    (S : Sylow 2 G) (hsylow : Nonempty (S ≃* W32))
    (hleft : CyclicQuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (Equiv.Perm (Fin 3))) : Alternative G₁ G₂ S := by
  let P : Sylow 2 (generalizedFitting G ⧸ center (generalizedFitting G)) := default
  let eS := Classical.choice hsylow
  have hP : Nat.card P = 32 := (component_quotient_sylow_card_of_top eG hK htop S P).trans
    ((Nat.card_congr eS.toEquiv).trans wreathedThirtyTwo_card)
  obtain ⟨p, hp, ho, hm⟩ := component_quotient_degree_three_of_wreathed32 hA hC hH eG hK S eS P hP
  let : Fact p.Prime := ⟨hp⟩
  rcases hm with hm | hm
  · obtain ⟨F, hF, hfin, hc, ⟨j⟩⟩ := hm
    let E := ULift.{u} F
    let a : F ≃+* E := ULift.ringEquiv.symm
    have hE : Nat.card E = p := by simpa [E] using hc
    exact ten_linear_of_wreathed_source eG hK htop S hsylow hp ho hE
      (j.trans (Atlas.fieldEquivPSL 3 a)) hleft hright
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
    exact ten_unitary_of_wreathed_source eG hK htop S hsylow J' hp ho hE hJ'
      (j.trans b) hleft hright

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource

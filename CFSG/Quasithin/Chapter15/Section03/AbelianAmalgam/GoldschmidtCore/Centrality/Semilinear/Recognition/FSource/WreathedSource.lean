module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.DegreeThreeSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.WreathedModels

/-!
# Row (10) from the original wreathed Sylow and central-quotient model

The source quotient makes the component center odd. When the component
is the whole ambient group, its central quotient has the same Sylow order.
Its actual wreathed model fixes the linear/unitary sign. The earlier
scalar-cover and order calculations now assemble the exact row with the
original two local groups. There is no multiplier, sign, or prime-congruence
premise. Catalogue selection, ambient equality and local recognition are
the independent source inputs still supplied by the F.6 assembly.

Source: Aschbacher--Smith F.6.18(10), pp.309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H F : Type u} [Group G] [Finite G] [Group H] [Finite H]
    [Field F] [Finite F] {G₁ G₂ : Subgroup G}

theorem ten_linear_of_wreathed_source
    (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G)) (htop : generalizedFitting G = ⊤)
    (S : Sylow 2 G) (hsylow : Nonempty (S ≃* W32))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p)
    (eK : generalizedFitting G ⧸ center (generalizedFitting G) ≃* PSL(3,F))
    (hleft : CyclicQuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (Equiv.Perm (Fin 3))) : Alternative G₁ G₂ S := by
  let P : Sylow 2 (generalizedFitting G ⧸ center (generalizedFitting G)) := default
  let eS := Classical.choice hsylow
  have hP : Nat.card P = 32 := (component_quotient_sylow_card_of_top eG hK htop S P).trans
    ((Nat.card_congr eS.toEquiv).trans wreathedThirtyTwo_card)
  have hm := (component_linear_three_wreathed_models hK S eS P hP hp ho hcard eK).1
  exact ten_linear_of_source_component hK htop S hsylow hp hcard (by omega) eK hleft hright

theorem ten_unitary_of_wreathed_source
    (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G)) (htop : generalizedFitting G = ⊤)
    (S : Sylow 2 G) (hsylow : Nonempty (S ≃* W32))
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (eK : generalizedFitting G ⧸ center (generalizedFitting G) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J)
    (hleft : CyclicQuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (Equiv.Perm (Fin 3))) : Alternative G₁ G₂ S := by
  let P : Sylow 2 (generalizedFitting G ⧸ center (generalizedFitting G)) := default
  let eS := Classical.choice hsylow
  have hP : Nat.card P = 32 := (component_quotient_sylow_card_of_top eG hK htop S P).trans
    ((Nat.card_congr eS.toEquiv).trans wreathedThirtyTwo_card)
  have hm := (component_unitary_three_wreathed_models eG hK S eS P hP J hp ho hcard hconj eK).1
  exact ten_unitary_of_source_component eG hK htop S hsylow J hp hcard hconj (by omega) eK hleft hright

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource

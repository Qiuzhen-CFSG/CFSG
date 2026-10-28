module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.Setup
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.FixedCyclicRoot.TorusAction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.FixedCyclicRoot.TorusPlacement

/-!
# Fixed cyclic root coordinates over the original fixed field

This reduction supplies the marked involution and the fixed-field scalar
formula for every member of the generated actor subgroup, using one actual
projective conjugator. Both the field and the Hermitian involution are
unchanged. For p ≡ 1 modulo four, the fixed torus and its Weyl coset have
odd index in the entrywise fixed group. The proved torus placement therefore
supplies the conjugator for every larger fixed cyclic two-group.

The original conditional reduction is retained, and the final theorem
discharges its torus placement premise. The independent fixed-involution
extension belongs to the consumer's order-two branch.
Source: Aschbacher--Smith E.1.14(7), printed p.214; Aschbacher (1982),
Lemma 4.11.
-/

public section
open Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
variable {F : Type} [Field F]

/-- Discharge the entire root-action contract from the fixed torus conjugacy input. -/
theorem fixedCyclicRootCoordinates_of_torusPlacement
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (h2 : (2 : F) ≠ 0) (hplace : FixedCyclicTorusPlacement J hJ) :
    FixedCyclicRootCoordinates J := by
  intro γ hγ x hx hx2 hlarge w hw hwx
  obtain ⟨y, hy, c, hxc⟩ := hplace γ hγ x hx hx2 hlarge
  exact FixedCyclicRoot.rootActionCoordinates_of_fixed_conjugator
    J hJ h2 γ hγ x w y hy c hxc hw hwx

/-- Larger fixed cyclic two-groups have marked root coordinates for their
entire generated actor subgroup when p is 1 modulo four. -/
theorem fixedCyclicRootCoordinates [Finite F]
    (J : HermitianForm 3 F)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    FixedCyclicRootCoordinates J := by
  have h2 : (2 : F) ≠ 0 := by
    apply Ring.two_ne_zero
    intro hchar
    let := Fintype.ofFinite F
    have heven := FiniteField.even_card_of_char_two hchar
    rw [← Nat.card_eq_fintype_card, hcard] at heven
    have hodd : p ^ 2 % 2 = 1 := Nat.odd_iff.mp ho.pow
    omega
  exact fixedCyclicRootCoordinates_of_torusPlacement J hJ h2
    (fixedCyclicTorusPlacement J hJ hp ho hmod hcard hc)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement

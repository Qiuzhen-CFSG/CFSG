module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Supplement

/-!
# Assembly of the opposite-core transfer

The actual point transitivity supplies the supplement, and the elementary
quotient supplies the Frattini premise for 11.5.6(4). Parts (4--5), coprime
commutator idempotence, and conjugacy of the Cartan kernels under O₂(I)
then discharge the remaining algebraic premises of the core transfer.

The natural-quotient fixed-space bound and the geometric Cartan conjugacy
are still explicit premises. This conditional assembly does not assert
that either source input or the full 11.5.7 argument has been proved.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Assemble the transfer from the two still-open source inputs, retaining
the exact quotient denominator and the actual Cartan kernel. -/
theorem corePair_le_point_core_from_fixed_and_torus
    (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hV : V ≤ E.G₁.pCoreIn 2) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) y)
    (hodd : Odd (Nat.card (cartanKernel E)))
    (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁)
    (hXpoint : E.X ≤ normalizer (E.V₁.map (MulAut.conj y).toMonoidHom : Set G))
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hti : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hM3 : E.M₁ ≤ normalizer (E.V₃ : Set G))
    (hout : ¬ E.V₁.map (MulAut.conj y).toMonoidHom ≤ E.V₃)
    (htrans : ∀ A B : Subgroup G,
      (∃ g : G, A = E.V₁.map (MulAut.conj g).toMonoidHom) →
      (∃ g : G, B = E.V₁.map (MulAut.conj g).toMonoidHom) →
      A ≤ V → B ≤ V → ¬ A ≤ E.V₃ → ¬ B ≤ E.V₃ →
      ∃ l ∈ E.L₁, B = A.map (MulAut.conj l).toMonoidHom)
    (hG : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hfixed : corePair (auxiliaryW E) y ⊓ centralizer (cartanKernel E : Set G) ≤
      pairDenominator E y)
    (hconj : ∀ s ∈ oppositePointStabilizer E y,
      ∃ r ∈ (oppositeJoin (auxiliaryW E) y).pCoreIn 2,
        (cartanKernel E).map (MulAut.conj s).toMonoidHom =
          (cartanKernel E).map (MulAut.conj r).toMonoidHom) :
    corePair (auxiliaryW E) y ≤ E.G₁.pCoreIn 2 := by
  exact corePair_le_point_core_of_cartan E m hy hV hW hcore hXI hodd hfixed hG
    (point_stabilizer_supplement E m hy hti hM3 hout htrans)
    (stabilizer_normalizes_commutator_of_core_conjugacy E m hy hcore hXI hodd hconj)
    (cartan_commutator_KY_le_core E m hy hV hW hPhi hcore hXI hodd
      hXL hXG hXpoint hfour hfive)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient

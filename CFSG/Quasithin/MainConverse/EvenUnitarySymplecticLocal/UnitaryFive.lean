module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.MainConverse.EvenUnitarySymplecticLocal.UnitaryFive.Coverage
public import CFSG.Quasithin.MainConverse.EvenUnitarySymplecticLocal.UnitaryFive.ParabolicOrders
public import Theory.GroupTheory.TwoLocalConjugateCover
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourFormTransport
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourParabolicOrders
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourParabolicCores

/-!
# Quasithinness and even characteristic of PSU₅(4)

Every allowed nondegenerate Hermitian form is transported to the identity
Gram matrix by an actual projective group isomorphism. A cover of two-locals
by conjugates of the line and plane parabolics reduces QT to their orders:
the odd parts `3² * 5² * 13` and `3² * 5 * 17` are cube-free. The full
parabolics are two-local and have self-centralizing two-cores, so maximality
also gives the required characteristic-two condition.

The conditional reductions are retained, and the final theorems discharge
their premises using the geometric coverage, full parabolic orders and
intrinsic two-core centralizer calculations. The results apply to every
nondegenerate Hermitian form with the given field and Frobenius data.
The residual local groups in F.1.12(7) are smaller than the full parabolics;
all normality and core calculations here concern the full parabolics.

Source: Aschbacher–Smith, Theorem 0.1.2(1), printed pp.4 and 482, and
F.1.12(7), printed pp.263–264. The matrix field has order sixteen.
-/

namespace CFSG.Quasithin.MainConverse.UnitaryFive

open BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram
open Theory.SpecificGroups.UnitaryFive

variable {F : Type} [Field F]

/-- The full projective line (`false`) and plane (`true`) parabolics. -/
@[expose] public def standardParabolic (J : HermitianForm 5 F) (plane : Bool) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)) :=
  if plane then planeParabolic (identityGram J) else lineParabolic (identityGram J)

variable [Finite F] (J : HermitianForm 5 F)

attribute [local instance] finite_projective

/-- Conditional QT reduction using the orders of the full projective parabolics. -/
public theorem quasithin_of_parabolic_orders
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (hcover : ∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)),
      IsTwoLocal M → ∃ b g, M ≤ (standardParabolic J b).map (MulAut.conj g).toMonoidHom)
    (horders : ∀ b, ∃ a : ℕ, Nat.card (standardParabolic J b) ∣
      2 ^ a * (if b then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13)) :
    IsQuasithin (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨e⟩ := projective_equiv_identity_four J hcard hconj
  apply Theory.GroupTheory.isQuasithin_of_equiv e.symm
  apply CFSG.Quasithin.isQuasithin_iff_twoLocal.mpr
  intro M hM p hp ho
  apply Theory.GroupTheory.primeRank_le_of_twoLocal_conjugate_cover
    (standardParabolic J) p 2 _ hcover M hM
  intro b
  obtain ⟨a, ha⟩ := horders b
  exact primeRank_le_two_of_parabolic_order_dvd a b ha hp ho

/-- The same reduction in the form consumed by a specific two-local. -/
public theorem twoLocal_rank_of_parabolic_orders
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (hcover : ∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)),
      IsTwoLocal M → ∃ b g, M ≤ (standardParabolic J b).map (MulAut.conj g).toMonoidHom)
    (horders : ∀ b, ∃ a : ℕ, Nat.card (standardParabolic J b) ∣
      2 ^ a * (if b then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13))
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsTwoLocal M)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p M ≤ 2 :=
  CFSG.Quasithin.isQuasithin_iff_twoLocal.mp
    (quasithin_of_parabolic_orders J hcard hconj hcover horders) M hM p hp ho

/-- Maximality identifies the local with a parabolic conjugate, so the intrinsic
two-core centralizer bound transfers through the actual group equivalence. -/
public theorem maximalTwoLocal_core_of_parabolic_cover
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (hcover : ∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)),
      IsTwoLocal M → ∃ b g, M ≤ (standardParabolic J b).map (MulAut.conj g).toMonoidHom)
    (hlocal : ∀ b, IsTwoLocal (standardParabolic J b))
    (hcore : ∀ b, Subgroup.centralizer
      (pCore 2 (standardParabolic J b) : Set (standardParabolic J b)) ≤
        pCore 2 (standardParabolic J b))
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsMaximalTwoLocal M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
  obtain ⟨e⟩ := projective_equiv_identity_four J hcard hconj
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e M).mp
  exact Theory.GroupTheory.centralizer_pCore_le_of_twoLocal_conjugate_cover
    (standardParabolic J) hlocal hcore hcover (M.map e.toMonoidHom)
    (Theory.Quasithin.isMaximalTwoLocal_map e hM)

/-- Conditional E reduction, with the full parabolics’ two-cores. -/
public theorem evenCharacteristic_of_parabolic_cover
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (hcover : ∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)),
      IsTwoLocal M → ∃ b g, M ≤ (standardParabolic J b).map (MulAut.conj g).toMonoidHom)
    (hlocal : ∀ b, IsTwoLocal (standardParabolic J b))
    (hcore : ∀ b, Subgroup.centralizer
      (pCore 2 (standardParabolic J b) : Set (standardParabolic J b)) ≤
        pCore 2 (standardParabolic J b)) :
    IsEvenCharacteristic (ProjectiveSpecialUnitaryMatrixGroup J) := by
  intro T M hM _
  exact maximalTwoLocal_core_of_parabolic_cover J hcard hconj hcover hlocal hcore M hM

private theorem standardParabolic_cover
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)))
    (hM : IsTwoLocal M) :
    ∃ b g, M ≤ (standardParabolic J b).map (MulAut.conj g).toMonoidHom := by
  let := charP_two_of_card_sixteen hcard
  exact Coverage.twoLocal_parabolic_cover (identityGram J) hcard hconj rfl M hM

private theorem standardParabolic_orders
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (b : Bool) :
    ∃ a : ℕ, Nat.card (standardParabolic J b) ∣
      2 ^ a * (if b then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13) := by
  let := charP_two_of_card_sixteen hcard
  refine ⟨20, ?_⟩
  cases b
  · exact (card_lineParabolic (identityGram J) hcard hconj rfl).dvd
  · exact (card_planeParabolic (identityGram J) hcard hconj rfl).dvd

private theorem standardParabolic_isTwoLocal (hcard : Nat.card F = 16) (b : Bool) :
    IsTwoLocal (standardParabolic J b) := by
  let := charP_two_of_card_sixteen hcard
  exact Coverage.parabolic_isTwoLocal (identityGram J) rfl b

private theorem standardParabolic_core
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (b : Bool) :
    Subgroup.centralizer (pCore 2 (standardParabolic J b) : Set (standardParabolic J b)) ≤
      pCore 2 (standardParabolic J b) := by
  let := charP_two_of_card_sixteen hcard
  cases b
  · exact lineParabolic_centralizer_twoCore_le (identityGram J) hcard hconj rfl
  · exact planeParabolic_centralizer_twoCore_le (identityGram J) hcard hconj rfl

/-- PSU₅(4) is quasithin for every nondegenerate Hermitian form with the
specified involution. All parabolic premises are discharged. -/
public theorem quasithin
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) :
    IsQuasithin (ProjectiveSpecialUnitaryMatrixGroup J) :=
  quasithin_of_parabolic_orders J hcard hconj
    (standardParabolic_cover J hcard hconj) (standardParabolic_orders J hcard hconj)

/-- Every actual two-local of PSU₅(4) has odd-prime rank at most two. -/
public theorem twoLocal_rank
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsTwoLocal M)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p M ≤ 2 :=
  CFSG.Quasithin.isQuasithin_iff_twoLocal.mp (quasithin J hcard hconj) M hM p hp ho

/-- Every maximal two-local of PSU₅(4) has a self-centralizing intrinsic
two-core. In particular this applies to those containing an ambient Sylow
two-subgroup, as required by the source even-characteristic condition. -/
public theorem maximalTwoLocal_core
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsMaximalTwoLocal M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
  maximalTwoLocal_core_of_parabolic_cover J hcard hconj
    (standardParabolic_cover J hcard hconj) (standardParabolic_isTwoLocal J hcard)
    (standardParabolic_core J hcard hconj) M hM

/-- PSU₅(4) has even characteristic for every allowed nondegenerate form. -/
public theorem evenCharacteristic
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) :
    IsEvenCharacteristic (ProjectiveSpecialUnitaryMatrixGroup J) := by
  intro T M hM _
  exact maximalTwoLocal_core J hcard hconj M hM

end CFSG.Quasithin.MainConverse.UnitaryFive

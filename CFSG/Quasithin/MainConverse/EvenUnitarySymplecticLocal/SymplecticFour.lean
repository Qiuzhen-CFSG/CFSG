module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Defs
public import Theory.Quasithin.EvenCharacteristic
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicRanks
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover

/-!
# Quasithin and even characteristic for PSp₄(2^f), f ≥ 2

The actual central quotient is identified with the matrix group by the proved
trivial-center calculation. Both full standard parabolics are two-local and
have self-centralizing intrinsic two-cores. Thus geometric coverage by
conjugate parabolics identifies every maximal two-local with a parabolic and
gives condition E. For QT, the same coverage transfers the parabolics' odd-prime
rank bounds to every two-local.

The fixed-space radical supplies the parabolic coverage, and the determinant
characters account for the torus contribution to the full parabolic rank bounds.
The final theorems discharge both inputs to the retained conditional reductions,
proving QT and E on the actual central quotient. Only finite-field cardinality
and f ≥ 2 are assumed; simplicity and the proper-K clause belong to the parent
converse assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(1), printed pp.3–4; repeated as Theorem 0.1.1(1), printed pp.481–482.
The parabolic matrix calculations use F.1.12(I)(2), printed pp.262–264.
-/

namespace CFSG.Quasithin.MainConverse.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open Theory.GroupTheory

variable {F : Type*} [Field F] [Finite F]

private theorem primeRank_le_of_conjugate_le (p : ℕ) (M P : Subgroup (Sp F))
    (g : Sp F) (h : M.map (MulAut.conj g).toMonoidHom ≤ P) :
    primeRank p M ≤ primeRank p P := by
  rw [primeRank_equiv p ((MulAut.conj g).subgroupMap M)]
  exact primeRank_le_of_injective p (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

/-- Conditional reduction: coverage by conjugate full parabolics and their
odd-prime rank bounds suffice for every two-local rank bound. -/
public theorem matrix_twoLocal_rank_of_parabolic_cover
    (hcover : ∀ M : Subgroup (Sp F), IsTwoLocal M → ∃ g : Sp F,
      M.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      M.map (MulAut.conj g).toMonoidHom ≤ planeParabolic)
    (hrank : ∀ p : ℕ, p.Prime → Odd p →
      primeRank p (pointParabolic (F := F)) ≤ 2 ∧
      primeRank p (planeParabolic (F := F)) ≤ 2)
    (M : Subgroup (Sp F)) (hM : IsTwoLocal M) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p M ≤ 2 := by
  obtain ⟨g, h | h⟩ := hcover M hM
  · exact (primeRank_le_of_conjugate_le p M _ g h).trans (hrank p hp ho).1
  · exact (primeRank_le_of_conjugate_le p M _ g h).trans (hrank p hp ho).2

/-- Conditional reduction: a maximal two-local covered by a full parabolic
is that parabolic, whose intrinsic two-core is proved self-centralizing. -/
public theorem matrix_maximalTwoLocal_core_of_parabolic_cover
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    (hcover : ∀ M : Subgroup (Sp F), IsTwoLocal M → ∃ g : Sp F,
      M.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      M.map (MulAut.conj g).toMonoidHom ≤ planeParabolic)
    (M : Subgroup (Sp F)) (hM : IsMaximalTwoLocal M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  obtain ⟨g, h | h⟩ := hcover M hM.1
  · have hm := isMaximalTwoLocal_map (MulAut.conj g) hM
    have he : M.map (MulAut.conj g).toMonoidHom = pointParabolic :=
      le_antisymm h (hm.2 (pointParabolic_isTwoLocal hF (by omega)) h)
    apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 (MulAut.conj g) M).mp
    rw [he]
    exact pointParabolic_selfCentralizing_core hF (by omega)
  · have hm := isMaximalTwoLocal_map (MulAut.conj g) hM
    have he : M.map (MulAut.conj g).toMonoidHom = planeParabolic :=
      le_antisymm h (hm.2 (planeParabolic_isTwoLocal hF (by omega)) h)
    apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 (MulAut.conj g) M).mp
    rw [he]
    exact planeParabolic_selfCentralizing_core hF (by omega)

/-- Conditional QT reduction on the exact central-quotient carrier. -/
public theorem projective_quasithin_of_parabolic_cover
    {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hcover : ∀ M : Subgroup (Sp F), IsTwoLocal M → ∃ g : Sp F,
      M.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      M.map (MulAut.conj g).toMonoidHom ≤ planeParabolic)
    (hrank : ∀ p : ℕ, p.Prime → Odd p →
      primeRank p (pointParabolic (F := F)) ≤ 2 ∧
      primeRank p (planeParabolic (F := F)) ≤ 2) :
    IsQuasithin (ClassicalGroup.PSp 2 F) := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  have hqt : IsQuasithin (Sp F) := isQuasithin_iff_twoLocal.mpr fun M hM p hp ho =>
    matrix_twoLocal_rank_of_parabolic_cover hcover hrank M hM hp ho
  exact isQuasithin_of_equiv EvenProjective.equiv hqt

/-- Conditional E reduction using the proved matrix-to-projective equivalence.
This reduction keeps the geometric coverage premise explicit. -/
public theorem projective_evenCharacteristic_of_parabolic_cover
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    (hcover : ∀ M : Subgroup (Sp F), IsTwoLocal M → ∃ g : Sp F,
      M.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      M.map (MulAut.conj g).toMonoidHom ≤ planeParabolic) :
    IsEvenCharacteristic (ClassicalGroup.PSp 2 F) := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  have he : IsEvenCharacteristic (Sp F) := fun _ M hM _ =>
    matrix_maximalTwoLocal_core_of_parabolic_cover hF hf hcover M hM
  exact he.of_equiv EvenProjective.equiv

/-- Every two-local of Sp₄(2^f), f ≥ 2, has odd-prime rank at most two.
Both full-parabolic rank bounds and the coverage premise are discharged. -/
public theorem matrix_twoLocal_rank
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    (M : Subgroup (Sp F)) (hM : IsTwoLocal M) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p M ≤ 2 :=
  matrix_twoLocal_rank_of_parabolic_cover (twoLocal_parabolic_cover hF hf)
    (parabolics_odd_primeRank_le_two_of_card hF) M hM hp ho

/-- Every maximal two-local of Sp₄(2^f), f ≥ 2, has a self-centralizing
intrinsic two-core, since it is conjugate to a full standard parabolic. -/
public theorem matrix_maximalTwoLocal_core
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    (M : Subgroup (Sp F)) (hM : IsMaximalTwoLocal M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
  matrix_maximalTwoLocal_core_of_parabolic_cover hF hf
    (twoLocal_parabolic_cover hF hf) M hM

/-- The actual central quotient PSp₄(2^f), f ≥ 2, satisfies condition QT. -/
public theorem projective_quasithin
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) :
    IsQuasithin (ClassicalGroup.PSp 2 F) :=
  projective_quasithin_of_parabolic_cover hF (twoLocal_parabolic_cover hF hf)
    (parabolics_odd_primeRank_le_two_of_card hF)

/-- The actual central quotient PSp₄(2^f), f ≥ 2, satisfies condition E. -/
public theorem projective_evenCharacteristic
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) :
    IsEvenCharacteristic (ClassicalGroup.PSp 2 F) :=
  projective_evenCharacteristic_of_parabolic_cover hF hf (twoLocal_parabolic_cover hF hf)

/-- The explicit two-local odd-prime rank bound on the projective carrier. -/
public theorem projective_twoLocal_rank
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    (M : Subgroup (ClassicalGroup.PSp 2 F)) (hM : IsTwoLocal M)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p M ≤ 2 :=
  isQuasithin_iff_twoLocal.mp (projective_quasithin hF hf) M hM p hp ho

/-- The source centralizer condition for every maximal two-local containing
an ambient Sylow two-subgroup of the actual projective carrier. -/
public theorem projective_maximalTwoLocal_core
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    (T : Sylow 2 (ClassicalGroup.PSp 2 F))
    (M : Subgroup (ClassicalGroup.PSp 2 F)) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup (ClassicalGroup.PSp 2 F)) ≤ M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
  projective_evenCharacteristic hF hf T M hM hTM

end CFSG.Quasithin.MainConverse.SymplecticFour

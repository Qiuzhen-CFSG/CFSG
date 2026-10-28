module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtAlternatives.Models
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtReduction
public import Theory.GroupTheory.PResidual.Defs

/-!
# The complete thirteen alternatives of F.6.18

Every local clause is attached to the actual generating subgroups and their
intersection. In row (3), the factors are embedded in the ambient group and their
internal direct product is the literal two-residual. Rows (6)–(9) retain the
triple covers; rows (8) and (11) retain their field and graph actions. The sign
in rows (10)–(11) is fixed by the prime modulo four.

The printed list uses chosen names for the generators. This is explicit in
F.1.12(I), which chooses the side centralizing the Sylow center, and in the proof
of F.6.17, which chooses L₁ inside the component. Neither F.6.1 nor F.6.2 imposes
that ordering on an input pair. Accordingly `Alternatives` allows either ordering
of the complete list, rather than imposing the asymmetric rows on an arbitrary
ordered pair. This does not change the common Sylow subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.1–2 p.304, F.6.15–18 pp.308–310, F.1.12 pp.262–263.
This is an interface for the explicitly parameterized universal theorem.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.GoldschmidtAlternatives
universe u

variable {G : Type u} [Group G]

/-- Conjugation by t normalizes K and is not conjugation by any element of K. -/
def OuterOn (K : Subgroup G) (t : G) : Prop :=
  t ∈ normalizer K ∧ ¬ ∃ k : K, ∀ x : K,
    t * x.val * t⁻¹ = k.val * x.val * k.val⁻¹

/-- F.6.18(1), with both intrinsic local cores and the actual three-core. -/
def Case1 (G₁ G₂ : Subgroup G) : Prop :=
  Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* C 2) ∧
    pCore 2 G₁ = ⊥ ∧ pCore 2 G₂ = ⊥ ∧ ¬ IsCyclic (pCore 3 G)

/-- F.6.18(2); 3^(1+2) is the concrete exponent-three Heisenberg group. -/
def Case2 (G : Type u) [Group G] : Prop :=
  Nonempty (G ≃* S3 × S3) ∨ Extension G (HeisenbergPrime 3) E4

/-- F.6.18(3). The direct factors are embedded in G and their join is
its two-residual, not its two-core. -/
def Case3 (G₁ G₂ : Subgroup G) : Prop :=
  ∃ (p : ℕ) (K D : Subgroup G), p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
    ClassicalGroup.IsPSL K 2 p ∧ Nonempty (D ≃* C 3) ∧
    K ⊔ D = pResidual 2 G ∧ Disjoint K D ∧
    (∀ k : K, ∀ d : D, Commute (k : G) (d : G)) ∧
    Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4) ∧
    Nonempty (G₁ ≃* DihedralGroup 12) ∧ Nonempty (G₂ ≃* S4) ∧
    (∃ t ∈ G₁ ⊓ G₂, t ∉ K) ∧
    (∀ t ∈ G₁ ⊓ G₂, t ∉ K → OuterOn K t ∧ OuterOn D t)

/-- F.6.18(4). -/
def Case4 (G₁ G₂ : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
    ClassicalGroup.IsPSL G 2 p ∧
    Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* E4) ∧
    Nonempty (G₁ ≃* DihedralGroup 6) ∧ Nonempty (G₂ ≃* DihedralGroup 6)

/-- F.6.18(5). -/
def Case5 (G₁ G₂ : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧ PGLTwo G p ∧
    Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4) ∧
    Nonempty (G₁ ≃* DihedralGroup 12) ∧ Nonempty (G₂ ≃* S4)

/-- F.6.18(6), retaining the triple cover and both allowed field degrees. -/
def Case6 (G₁ G₂ : Subgroup G) : Prop :=
  (TripleAlternating G 6 ∨
    ∃ p e : ℕ, p.Prime ∧ 0 < e ∧ e ≤ 2 ∧
      (p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) ∧ ClassicalGroup.IsPSL G 2 (p ^ e)) ∧
    Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4) ∧
    Nonempty (G₁ ≃* S4) ∧ Nonempty (G₂ ≃* S4)

/-- F.6.18(7). The slash in the second local group does not assert splitting. -/
def Case7 (G₁ G₂ : Subgroup G) : Prop :=
  (Nonempty (G ≃* alternatingGroup (Fin 7)) ∨ TripleAlternating G 7) ∧
    Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4) ∧
    Nonempty (G₁ ≃* S4) ∧ Extension G₂ (C 3 × E4) (C 2)

/-- F.6.18(8), with the actual Frobenius action over the quadratic field. -/
def Case8 (G₁ G₂ : Subgroup G) : Prop :=
  (TripleSymmetric G 6 ∨ ∃ p : ℕ, p.Prime ∧ p % 8 = 3 ∧ FieldExtension G p) ∧
    Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* C 2 × DihedralGroup 4) ∧
    Nonempty (G₁ ≃* C 2 × S4) ∧ Nonempty (G₂ ≃* C 2 × S4)

/-- F.6.18(9). -/
def Case9 (G₁ G₂ : Subgroup G) : Prop :=
  (Nonempty (G ≃* Equiv.Perm (Fin 7)) ∨ TripleSymmetric G 7) ∧
    Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* C 2 × DihedralGroup 4) ∧
    Nonempty (G₁ ≃* C 2 × S4) ∧ Nonempty (G₂ ≃* S3 × DihedralGroup 4)

/-- F.6.18(10). The sign is fixed by p modulo four: linear at 5 modulo
8, unitary at 3 modulo 8. Both special and projective groups are retained. -/
def Case10 (G₁ G₂ : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧
    ((p % 8 = 5 ∧ LinearThree G p) ∨ (p % 8 = 3 ∧ UnitaryThree G p)) ∧
    Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* RegularWreathProduct (C 4) (C 2)) ∧
    Extension G₁ QuaternionCyclic.Model S3 ∧ Extension G₂ C4Square S3

/-- F.6.18(11); graph action, quaternion central square, and both local
extension maps are retained. -/
def Case11 (G₁ G₂ : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧
    ((p % 8 = 5 ∧ LinearGraphExtension G p) ∨
      (p % 8 = 3 ∧ UnitaryGraphExtension G p)) ∧
    Extension (G₁ ⊓ G₂ : Subgroup G) C4Square E4 ∧
    QuaternionSquareExtension G₁ S3 ∧ Extension G₂ C4Square (DihedralGroup 6)

/-- F.6.18(12), using the full automorphism group of the concrete Witt design. -/
def Case12 (G₁ G₂ : Subgroup G) : Prop :=
  Nonempty (G ≃* Sporadic.Mathieu.M12) ∧
    Extension (G₁ ⊓ G₂ : Subgroup G) C4Square E4 ∧
    QuaternionSquareExtension G₁ S3 ∧ Extension G₂ C4Square (DihedralGroup 6)

/-- F.6.18(13). The final local group has the full two-stage extension
C₂/(C₃ × E₄)/C₄², with an actual normal subgroup at the first stage. -/
def Case13 (G₁ G₂ : Subgroup G) : Prop :=
  Nonempty (G ≃* MulAut Sporadic.Mathieu.M12) ∧
    Extension (G₁ ⊓ G₂ : Subgroup G) C4Square (DihedralGroup 4) ∧
    QuaternionSquareExtension G₁ (DihedralGroup 6) ∧
    ∃ (N : Subgroup G₂) (_ : N.Normal), Nonempty (N ≃* C4Square) ∧
      Extension (G₂ ⧸ N) (C 3 × E4) (C 2)

/-- The twelve source rows that are retained after excluding row (1). -/
def RemainingOrdered (G₁ G₂ : Subgroup G) : Prop :=
  Case2 G ∨ Case3 G₁ G₂ ∨ Case4 G₁ G₂ ∨ Case5 G₁ G₂ ∨
    Case6 G₁ G₂ ∨ Case7 G₁ G₂ ∨ Case8 G₁ G₂ ∨ Case9 G₁ G₂ ∨
    Case10 G₁ G₂ ∨ Case11 G₁ G₂ ∨ Case12 G₁ G₂ ∨ Case13 G₁ G₂

/-- F.6.18 uses the naming convention of its proof (F.6.17 chooses L₁≤K,
and F.1.12(I) chooses the centralizing side). No ordering of an input pair
is assumed: either orientation of all local clauses is allowed. -/
def Remaining (G₁ G₂ : Subgroup G) : Prop :=
  RemainingOrdered G₁ G₂ ∨ RemainingOrdered G₂ G₁

/-- All thirteen rows, including the choice of names for the generators. -/
def Alternatives (G₁ G₂ : Subgroup G) : Prop :=
  (Case1 G₁ G₂ ∨ RemainingOrdered G₁ G₂) ∨
    (Case1 G₂ G₁ ∨ RemainingOrdered G₂ G₁)


/-- The surviving list is independent of the naming of the generators. -/
theorem remaining_symm {G : Type u} [Group G] {G₁ G₂ : Subgroup G}
    (h : Remaining G₁ G₂) : Remaining G₂ G₁ := h.symm

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.GoldschmidtAlternatives

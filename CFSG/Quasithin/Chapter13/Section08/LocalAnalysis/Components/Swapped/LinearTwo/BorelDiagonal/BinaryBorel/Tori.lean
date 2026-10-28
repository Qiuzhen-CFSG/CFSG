module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.BinaryBorel.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Compatible torus quotients of a binary product Borel

Each torus is the literal quotient of its factor normalizer by its own
two-core. The concrete model proves that it is cyclic of order 2ⁿ − 1.
The pair of quotient maps has kernel exactly the product Borel’s two-core;
the first isomorphism theorem supplies the marked quotient coordinates.
Both quotient maps and their commuting formula are retained.

Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952/PDF p.969.
-/

@[expose] public section

open Subgroup
open Matrix.ProjectiveSpecialLinearGroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.BinaryBorel
variable {Q : Type*} [Group Q] [Finite Q]

/-- The literal two-core quotient of a factor Borel. -/
abbrev Torus (S : Sylow 2 Q) := borel S ⧸ pCore 2 (borel S)

/-- The canonical surjection onto the actual torus quotient. -/
def torusMap (S : Sylow 2 Q) : borel S →* Torus S := QuotientGroup.mk' _

omit [Finite Q] in
theorem torusMap_surjective (S : Sylow 2 Q) : Function.Surjective (torusMap S) :=
  QuotientGroup.mk'_surjective _

omit [Finite Q] in
theorem torusMap_ker (S : Sylow 2 Q) : (torusMap S).ker = pCore 2 (borel S) :=
  QuotientGroup.ker_mk' _

theorem torus_cyclic {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (S : Sylow 2 Q) : IsCyclic (Torus S) := (factor_facts hn hmodel S).2.2.1

theorem torus_card {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (S : Sylow 2 Q) : Nat.card (Torus S) = 2 ^ n - 1 := (factor_facts hn hmodel S).2.2.2.1

/-- An actual equivalence identifying the two cyclic torus carriers of equal order. -/
noncomputable def torusEquiv {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) (S T : Sylow 2 Q) :
    Torus S ≃* Torus T := by
  let _ := torus_cyclic hn hmodel S
  let _ := torus_cyclic hn hmodel T
  exact mulEquivOfCyclicCardEq ((torus_card hn hmodel S).trans (torus_card hn hmodel T).symm)

/-- The pair of canonical factor quotient maps in the marked Borel coordinates. -/
noncomputable def productMap (S : Sylow 2 (Q × Q)) :
    borel S →* Torus (firstSylow S) × Torus (secondSylow S) :=
  ((torusMap (firstSylow S)).prodMap (torusMap (secondSylow S))).comp
    (coordinates S).toMonoidHom

theorem productMap_apply (S : Sylow 2 (Q × Q)) (x : borel S) :
    productMap S x = (torusMap (firstSylow S) (coordinates S x).1,
      torusMap (secondSylow S) (coordinates S x).2) := rfl

theorem productMap_surjective (S : Sylow 2 (Q × Q)) :
    Function.Surjective (productMap S) := by
  rintro ⟨a, b⟩
  obtain ⟨x, rfl⟩ := torusMap_surjective (firstSylow S) a
  obtain ⟨y, rfl⟩ := torusMap_surjective (secondSylow S) b
  exact ⟨(coordinates S).symm (x, y), by simp [productMap]⟩

/-- The kernel of the pair of torus maps is exactly the product Borel’s two-core. -/
theorem productMap_ker (S : Sylow 2 (Q × Q)) :
    (productMap S).ker = pCore 2 (borel S) := by
  ext x
  rw [MonoidHom.mem_ker, productMap_apply, Prod.mk_eq_one,
    ← MonoidHom.mem_ker, ← MonoidHom.mem_ker, torusMap_ker, torusMap_ker,
    twoCore, twoCore, twoCore]
  change (x : Q × Q).1 ∈ (firstSylow S : Subgroup Q) ∧
    (x : Q × Q).2 ∈ (secondSylow S : Subgroup Q) ↔ (x : Q × Q) ∈ (S : Subgroup _)
  rw [sylow_eq_prod S]
  rfl

/-- The first isomorphism theorem, retaining both torus coordinates. -/
noncomputable def torusCoordinates (S : Sylow 2 (Q × Q)) :
    Torus S ≃* Torus (firstSylow S) × Torus (secondSylow S) :=
  (QuotientGroup.quotientMulEquivOfEq (productMap_ker S).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (productMap_surjective S))

theorem torusCoordinates_mk (S : Sylow 2 (Q × Q)) (x : borel S) :
    torusCoordinates S (torusMap S x) = productMap S x := rfl


end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.BinaryBorel

end

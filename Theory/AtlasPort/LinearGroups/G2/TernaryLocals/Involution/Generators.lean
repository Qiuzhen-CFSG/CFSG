module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution.Coordinates

/-!
# Concrete root generators in the ternary involution centralizer

The roots B and D have weight one under the marked torus involution. Together
with their opposites and `torus 1 (-1)`, they therefore generate a subgroup
inside its actual centralizer. This module supplies two quaternion generator
pairs with common nonidentity square, verifies the binary-tetrahedral cubic
action in each root factor, and checks that the two opposite-root pairs
commute across the factors. Every relation is checked on the three octonion
algebra generators from `Coordinates`.

These are concrete relations, not an assumed centralizer configuration.
The order of `generated` and its intrinsic two-core centralizer are separate
prerequisites. A proof that `generated` has order 576 identifies it with the
full centralizer using the independently proved frame bound.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
I.4(G1), printed p.417, and Main Theorem 0.1.2(4), printed pp.3–4, repeated on
pp.481–482. Root and torus coordinates use the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.TernaryLocals.Involution
open Atlas.SplitOctonion
set_option maxRecDepth 100000

/-- Long and short root elements, their opposite roots, and a nonsquare torus actor. -/
def ambientGenerator : Fin 5 → Model K :=
  ![rootB 1, longest * rootB 1 * longest⁻¹,
    rootD 1, longest * rootD 1 * longest⁻¹, torus 1 (-1)]

private def marks : Fin 3 → Carrier K := ![u,v,w]

private theorem ambient_ext (g h : Model K)
    (he : ∀ i j, g.val (marks i) j = h.val (marks i) j) : g = h := by
  apply ext_generators
  · exact funext (he 0)
  · exact funext (he 1)
  · exact funext (he 2)

private theorem local_ext (g h : P)
    (he : ∀ i j, g.val.val (marks i) j = h.val.val (marks i) j) : g = h :=
  Subtype.ext (ambient_ext g.val h.val he)

theorem ambientGenerator_commute (i : Fin 5) :
    ambientGenerator i * involution = involution * ambientGenerator i := by
  apply ambient_ext
  exact (by decide +kernel : ∀ i k j,
    (ambientGenerator i * involution).val (marks k) j =
    (involution * ambientGenerator i).val (marks k) j) i

/-- The five displayed elements inside the actual centralizer. -/
def generator (i : Fin 5) : P := ⟨ambientGenerator i, by
  rw [P, localSubgroup_false]
  exact Subgroup.mem_centralizer_singleton_iff.mpr (ambientGenerator_commute i)⟩

/-- The concrete subgroup whose equality with the centralizer is to be proved. -/
def generated : Subgroup P := Subgroup.closure (Set.range generator)

theorem generator_mem (i : Fin 5) : generator i ∈ generated :=
  Subgroup.subset_closure ⟨i,rfl⟩

/-- `false` denotes the long-root factor; `true` the short-root factor. -/
def positive (s : Bool) : P := generator (if s then 2 else 0)
def negative (s : Bool) : P := generator (if s then 3 else 1)
def torusActor : P := generator 4

def centralSign : P := ⟨involution, by
  rw [P, localSubgroup_false]
  exact Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem centralSign_sq : centralSign ^ 2 = 1 := Subtype.ext involution_sq

theorem centralSign_ne_one : centralSign ≠ 1 := by
  intro h
  exact involution_ne_one (congrArg Subtype.val h)

/-- Quaternion generators in each of the two rank-one factors. -/
def quaternionI (s : Bool) : P := positive s ^ 2 * negative s
def quaternionJ (s : Bool) : P := (positive s * negative s * positive s)⁻¹

theorem positive_mem (s : Bool) : positive s ∈ generated := generator_mem _
theorem negative_mem (s : Bool) : negative s ∈ generated := generator_mem _
theorem torusActor_mem : torusActor ∈ generated := generator_mem _

theorem quaternionI_mem (s : Bool) : quaternionI s ∈ generated :=
  generated.mul_mem (generated.pow_mem (positive_mem s) _) (negative_mem s)

theorem quaternionJ_mem (s : Bool) : quaternionJ s ∈ generated :=
  generated.inv_mem (generated.mul_mem
    (generated.mul_mem (positive_mem s) (negative_mem s)) (positive_mem s))

theorem quaternionI_sq (s : Bool) : quaternionI s ^ 2 = centralSign := by
  apply local_ext
  exact (by decide +kernel : ∀ s i j,
    ((quaternionI s ^ 2).val.val (marks i)) j = centralSign.val.val (marks i) j) s

theorem quaternionJ_sq (s : Bool) : quaternionJ s ^ 2 = centralSign := by
  apply local_ext
  exact (by decide +kernel : ∀ s i j,
    ((quaternionJ s ^ 2).val.val (marks i)) j = centralSign.val.val (marks i) j) s

theorem quaternionI_fourth (s : Bool) : quaternionI s ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, quaternionI_sq, centralSign_sq]

theorem quaternion_twist (s : Bool) :
    quaternionJ s * quaternionI s = (quaternionI s)⁻¹ * quaternionJ s := by
  apply local_ext
  exact (by decide +kernel : ∀ s i j,
    (quaternionJ s * quaternionI s).val.val (marks i) j =
    ((quaternionI s)⁻¹ * quaternionJ s).val.val (marks i) j) s

theorem positive_cube (s : Bool) : positive s ^ 3 = 1 := by
  apply local_ext
  exact (by decide +kernel : ∀ s i j,
    (positive s ^ 3).val.val (marks i) j = (1 : P).val.val (marks i) j) s

/-- The cubic action agrees with the standard binary-tetrahedral presentation. -/
theorem positive_conj_I (s : Bool) :
    positive s * quaternionI s * (positive s)⁻¹ = quaternionJ s * quaternionI s := by
  apply local_ext
  exact (by decide +kernel : ∀ s i j,
    (positive s * quaternionI s * (positive s)⁻¹).val.val (marks i) j =
    (quaternionJ s * quaternionI s).val.val (marks i) j) s

theorem positive_conj_J (s : Bool) :
    positive s * quaternionJ s * (positive s)⁻¹ = (quaternionI s)⁻¹ := by
  apply local_ext
  exact (by decide +kernel : ∀ s i j,
    (positive s * quaternionJ s * (positive s)⁻¹).val.val (marks i) j =
    ((quaternionI s)⁻¹).val.val (marks i) j) s

theorem centralSign_mem : centralSign ∈ generated := by
  rw [← quaternionI_sq false]
  exact generated.pow_mem (quaternionI_mem false) 2

/-- One of the two opposite-root generators of the indicated factor. -/
def rootGenerator (s opposite : Bool) : P := if opposite then negative s else positive s

/-- The two opposite-root pairs commute elementwise across the two factors. -/
theorem root_factors_commute (a b : Bool) :
    rootGenerator false a * rootGenerator true b =
      rootGenerator true b * rootGenerator false a := by
  apply local_ext
  exact (by decide +kernel : ∀ a b i j,
    (rootGenerator false a * rootGenerator true b).val.val (marks i) j =
    (rootGenerator true b * rootGenerator false a).val.val (marks i) j) a b

end Atlas.G2.TernaryLocals.Involution

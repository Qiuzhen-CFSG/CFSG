module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.SourceAlignment.Automorphisms
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Raw inputs to the triality Cartan alignment

The ambient data retain SQTK, the intrinsic generalized Fitting subgroup, the
nonabelian simple component, the Sylow subgroup, and the literal subgroup
products in A.3.15. The case-five data live in the actual automorphism group of
the supplied standard carrier. The original component is identified with that
carrier by a separate multiplicative equivalence in the assembly theorem.

A relative Cartan is expressed by its abelian odd complement properties inside
the stabilizer of the marked Sylow subgroup in I. In particular neither I nor H
is asserted normal in the whole automorphism group. This description uses no
standard torus, and contains no alignment or conjugacy conclusion. All products
are products of sets, not joins. The inner-diagonal part is intersected with the
actual FBD product, and every element of F follows the source field convention.

These are input contracts, not a proof of A.3.15 or a construction of its raw
witness. Source: Aschbacher–Smith, `refs/quasithin.pdf`, pp.50–51 and p.511;
Notation A.2.5, p.33; GLS3 §§2.3 and 2.5.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Triality.Standard

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment

/-- The ambient prime-subgroup hypotheses of the source case. -/
structure AmbientInput {J : Type*} [Group J]
    (κ : GroupClass) (D B : Subgroup J) (S : Sylow 2 J) (p : ℕ) : Prop where
  sqtk : IsSQTK κ J
  fitting : generalizedFitting J = D
  simple : IsSimpleGroup D
  nonabelian : ¬ IsMulCommutative D
  prime : p.Prime
  large : 3 < p
  p_group : IsPGroup p B
  inside : B ≤ D
  permutes : (B : Set J) * (S : Set J) = (S : Set J) * (B : Set J)
  three_residual : pResidual 3 B ≠ ⊥

/-- Normality is a consequence of the generalized-Fitting equality. -/
theorem AmbientInput.normal {J : Type*} [Group J] [Finite J]
    {κ : GroupClass} {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}
    (h : AmbientInput κ D B S p) : D.Normal := by
  rw [← h.fitting]
  infer_instance

/-- The image of a subgroup in the actual inner automorphism group. -/
def innerImage {G : Type*} [Group G] (B : Subgroup G) : Subgroup (MulAut G) :=
  B.map (MulAut.conj : G →* MulAut G)

/-- Automorphisms preserving the given subgroup of the carrier. -/
def automorphismNormalizer {G : Type*} [Group G] (T : Subgroup G) :
    Subgroup (MulAut G) := MulAction.stabilizer (MulAut G) T

@[simp] theorem mem_automorphismNormalizer {G : Type*} [Group G]
    (T : Subgroup G) (a : MulAut G) :
    a ∈ automorphismNormalizer T ↔ T.map a.toMonoidHom = T := Iff.rfl

/-- The odd abelian complement in the relative Sylow normalizer. -/
structure RelativeCartan {G : Type*} [Group G]
    (T : Subgroup G) (H I : Subgroup (MulAut G)) : Prop where
  le_inner : H ≤ I
  normalizes : H ≤ automorphismNormalizer T
  abelian : IsMulCommutative H
  odd : Odd (Nat.card H)
  disjoint : Disjoint (innerImage T) H
  product : (I ⊓ automorphismNormalizer T : Set (MulAut G)) =
    (innerImage T : Set (MulAut G)) * (H : Set (MulAut G))

/-- Every algebraic clause of the raw triality case A.3.15(5). -/
structure RawConfiguration (P : Parameters) (n : ℕ)
    (T B : Subgroup (Carrier P)) where
  q_eq : P.q = 2 ^ n
  degree_gt_one : 1 < n
  F : Subgroup (MulAut (Carrier P))
  H : Subgroup (MulAut (Carrier P))
  I : Subgroup (MulAut (Carrier P))
  f : ℕ
  field_cyclic : IsCyclic F
  field_order : Nat.card F = f
  field_degree : f ∣ n
  field_elements : ∀ a ∈ F, IsSourceFieldAutomorphism P a
  subgroup_product : (innerImage B : Set (MulAut (Carrier P))) ⊆
    (F : Set (MulAut (Carrier P))) * (H : Set (MulAut (Carrier P)))
  cartan : RelativeCartan T H I
  field_invariant : F ≤ normalizer H
  extension_product :
    (F : Set (MulAut (Carrier P))) * (innerImage B : Set (MulAut (Carrier P))) *
        (MulAut.innerSubgroup (Carrier P) : Set (MulAut (Carrier P))) =
      (H : Set (MulAut (Carrier P))) * (innerImage B : Set (MulAut (Carrier P))) *
        (MulAut.innerSubgroup (Carrier P) : Set (MulAut (Carrier P)))
  inner_diagonal_part : (I : Set (MulAut (Carrier P))) =
    ((F : Set (MulAut (Carrier P))) * (innerImage B : Set (MulAut (Carrier P))) *
        (MulAut.innerSubgroup (Carrier P) : Set (MulAut (Carrier P)))) ∩
      (innerDiagonal P : Set (MulAut (Carrier P)))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment

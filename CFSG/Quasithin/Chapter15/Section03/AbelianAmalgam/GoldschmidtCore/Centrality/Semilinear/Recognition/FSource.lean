module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.SourceQuotient
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.ModelExclusions
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.PGL2.Defs
public import Theory.SpecificGroups.SU3.PrimeOrderDivisibility
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.PSL2.OuterSolvable.Actions
public import Mathlib.GroupTheory.RegularWreathProduct

/-!
# Full conditional F.6.18 source interface

The thirteen alternatives retain the actual ambient group, common Sylow,
local groups, component embeddings, covers, finite-field parameters, and
field/graph actions. Slash notation is encoded by a normal subgroup and
actual kernel and quotient isomorphisms; no splitting is inferred from a
slash. The hatted alternating groups are quasisimple central triple covers.
The unitary parameter is the fixed-field order, with coefficient field of
its square order and its literal Frobenius involution.

`ClassificationInput` is the permitted universal source premise, not a
proved classification theorem. The Goldschmidt triple and the SQTK quotient
by O_{3'} are both required. The quasisimple-component assertions in rows
(4)--(13) retain the reduction proved in F.6.17 and the proof of F.6.18.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, F.6.1--2,
F.6.17--18, printed pp.304 and 309--310; cover convention A.3.5.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u

abbrev C (n : ℕ) := Multiplicative (ZMod n)
abbrev E4 := C 2 × C 2
abbrev C4Square := C 4 × C 4
abbrev W32 := RegularWreathProduct (C 4) (C 2)

/-- The source's extension notation, without a splitting assumption. -/
def Extension (D A B : Type*) [Group D] [Group A] [Group B] : Prop :=
  ∃ N : Subgroup D, ∃ _ : N.Normal,
    Nonempty (N ≃* A) ∧ Nonempty ((D ⧸ N) ≃* B)

/-- The intrinsic central product C₄ * Q₈. -/
structure CyclicQuaternionProduct (D : Type*) [Group D] where
  cyclic : Subgroup D
  quaternion : Subgroup D
  cyclicEquiv : cyclic ≃* C 4
  quaternionEquiv : quaternion ≃* QuaternionGroup 2
  commute : ∀ x ∈ cyclic, ∀ y ∈ quaternion, x * y = y * x
  intersection : Nat.card (cyclic ⊓ quaternion : Subgroup D) = 2
  generates : cyclic ⊔ quaternion = ⊤

/-- An extension whose kernel is the literal quaternion central product. -/
def QuaternionExtension (D B : Type*) [Group D] [Group B] : Prop :=
  ∃ N : Subgroup D, ∃ _ : N.Normal,
    Nonempty (QuaternionCentralProductData N) ∧ Nonempty ((D ⧸ N) ≃* B)

/-- An extension whose kernel is C₄ * Q₈. -/
def CyclicQuaternionExtension (D B : Type*) [Group D] [Group B] : Prop :=
  ∃ N : Subgroup D, ∃ _ : N.Normal,
    Nonempty (CyclicQuaternionProduct N) ∧ Nonempty ((D ⧸ N) ≃* B)

/-- A finite field with its actual prime-power parameter. -/
structure FieldParameter where
  Carrier : Type u
  [field : Field Carrier]
  [finite : Finite Carrier]
  prime : ℕ
  prime_isPrime : prime.Prime
  degree : ℕ
  degree_pos : 0 < degree
  card : Nat.card Carrier = prime ^ degree
attribute [instance] FieldParameter.field FieldParameter.finite

/-- The hatted alternating model, keeping its actual central quotient. -/
structure TripleAlternating (D : Type*) [Group D] (n : ℕ) : Prop where
  perfect : Group.IsPerfect D
  center : Nonempty (Subgroup.center D ≃* C 3)
  quotient : Nonempty ((D ⧸ Subgroup.center D) ≃* alternatingGroup (Fin n))

/-- The hatted symmetric extension: its derived subgroup is the triple
alternating cover, with the literal symmetric quotient and sign action on
its cubic kernel. -/
structure TripleSymmetric (D : Type*) [Group D] (n : ℕ) where
  kernel : Subgroup D
  [normal : kernel.Normal]
  kernelEquiv : kernel ≃* C 3
  quotientEquiv : (D ⧸ kernel) ≃* Equiv.Perm (Fin n)
  kernel_le : kernel ≤ commutator D
  derived : TripleAlternating (commutator D) n
  center_eq : (Subgroup.center (commutator D)).map (commutator D).subtype = kernel
  inverse_action : ∀ g : D,
    Equiv.Perm.sign (quotientEquiv (QuotientGroup.mk' kernel g)) = -1 →
      ∀ z : kernel, g * (z : D) * g⁻¹ = (z : D)⁻¹

/-- Exact (S)L₃^ε(p) models, with both special and projective options. -/
inductive DegreeThree (p : ℕ) (D : Type u) [Group D] : Prop
  | linear (F : Type u) [Field F] [Finite F]
      (card : Nat.card F = p) (sign : p % 4 = 1)
      (equiv : D ≃* SL(3,F))
  | projectiveLinear (F : Type u) [Field F] [Finite F]
      (card : Nat.card F = p) (sign : p % 4 = 1)
      (equiv : D ≃* PSL(3,F))
  | unitary (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F)
      (card : Nat.card F = p ^ 2) (frobenius : ∀ x, J.conj x = x ^ p)
      (sign : p % 4 = 3) (equiv : D ≃* J.specialSubgroup)
  | projectiveUnitary (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F)
      (card : Nat.card F = p ^ 2) (frobenius : ∀ x, J.conj x = x ^ p)
      (sign : p % 4 = 3) (equiv : D ≃* ProjectiveSpecialUnitaryMatrixGroup J)

/-- The graph action is specified on matrices or their actual scalar quotient.
For unitary models we use a standard orthonormal Gram matrix, so inverse
transpose is the graph action. -/
inductive DegreeThreeGraph (p : ℕ) (D : Type u) [Group D] (α : MulAut D) : Prop
  | linear (F : Type u) [Field F] [Finite F]
      (card : Nat.card F = p) (sign : p % 4 = 1)
      (equiv : D ≃* SL(3,F))
      (action : ∀ x, equiv (α x) = Matrix.PSL3.OuterSolvable.graphSL F (equiv x))
  | projectiveLinear (F : Type u) [Field F] [Finite F]
      (card : Nat.card F = p) (sign : p % 4 = 1)
      (equiv : D ≃* PSL(3,F))
      (action : ∀ x, equiv (α x) = Matrix.PSL3.OuterSolvable.graph F (equiv x))
  | unitary (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F)
      (card : Nat.card F = p ^ 2) (frobenius : ∀ x, J.conj x = x ^ p)
      (sign : p % 4 = 3) (gram : J.form = 1) (equiv : D ≃* J.specialSubgroup)
      (action : ∀ x, (equiv (α x)).val.val = (equiv x).val.inv.transpose)
  | projectiveUnitary (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F)
      (card : Nat.card F = p ^ 2) (frobenius : ∀ x, J.conj x = x ^ p)
      (sign : p % 4 = 3) (gram : J.form = 1)
      (equiv : D ≃* ProjectiveSpecialUnitaryMatrixGroup J)
      (graphLift : MulAut J.specialSubgroup)
      (lift_action : ∀ x, (graphLift x).val.val = x.val.inv.transpose)
      (action : ∀ x, equiv (α (equiv.symm (J.specialToProjective x))) =
        J.specialToProjective (graphLift x))

/-- Discarding the action preserves the exact matrix-group model. -/
theorem DegreeThreeGraph.model {p : ℕ} {D : Type u} [Group D] {α : MulAut D}
    (h : DegreeThreeGraph p D α) : DegreeThree p D := by
  cases h with
  | linear F hc hs e _ => exact .linear F hc hs e
  | projectiveLinear F hc hs e _ => exact .projectiveLinear F hc hs e
  | unitary F J hc hf hs _ e _ => exact .unitary F J hc hf hs e
  | projectiveUnitary F J hc hf hs _ e _ _ _ => exact .projectiveUnitary F J hc hf hs e

variable {D : Type u} [Group D] [Finite D]

/-- Row (3)'s product and literal outer actions in the source residual. -/
structure ProductRow (S : Sylow 2 D) where
  field : FieldParameter.{u}
  degree : field.degree = 1
  congruence : field.prime % 24 = 11 ∨ field.prime % 24 = 13
  first : Subgroup D
  second : Subgroup D
  firstEquiv : first ≃* PSL(2,field.Carrier)
  secondEquiv : second ≃* C 3
  product : (first × second) ≃* ↥(first ⊔ second)
  product_apply : ∀ a b, (product (a,b) : D) = (a : D) * (b : D)
  residual : pResidual 2 D = first ⊔ second
  element : D
  mem_sylow : element ∈ S
  outside : element ∉ first
  firstOuter : InducesOuter first element
  secondOuter : InducesOuter second element

/-- The actual PSL₂ component and its field involution in row (8). -/
structure FieldExtensionRow where
  field : FieldParameter.{u}
  degree : field.degree = 2
  congruence : field.prime % 8 = 3
  componentEquiv : generalizedFitting D ≃* PSL(2,field.Carrier)
  automorphism : field.Carrier ≃+* field.Carrier
  frobenius : ∀ x, automorphism x = x ^ field.prime
  element : D
  involution : orderOf element = 2
  outside : element ∉ generalizedFitting D
  generated : generalizedFitting D ⊔ zpowers element = ⊤
  action : ∀ x : generalizedFitting D,
    ∃ y : generalizedFitting D,
      (y : D) = element * (x : D) * element⁻¹ ∧
      componentEquiv y = Theory.PSL2.OuterSolvable.projectiveFieldAutHom automorphism
        (componentEquiv x)

/-- The actual component and literal graph involution in row (11). -/
structure GraphExtensionRow where
  prime : ℕ
  prime_isPrime : prime.Prime
  congruence : prime % 8 = 3 ∨ prime % 8 = 5
  automorphism : MulAut (generalizedFitting D)
  model : DegreeThreeGraph prime (generalizedFitting D) automorphism
  element : D
  involution : orderOf element = 2
  outside : element ∉ generalizedFitting D
  generated : generalizedFitting D ⊔ zpowers element = ⊤
  action : ∀ x : generalizedFitting D,
    (automorphism x : D) = element * (x : D) * element⁻¹

/-- The complete numbered list. Local groups are the actual two generators,
and S is their actual intersection. No rank-one or representation assumption
is imposed on this source conclusion. -/
inductive Alternative (G₁ G₂ : Subgroup D) (S : Sylow 2 D) : Prop
  | one (sylow : Nonempty (S ≃* C 2))
      (leftCore : pCore 2 G₁ = ⊥) (rightCore : pCore 2 G₂ = ⊥)
      (noncyclic : ¬ IsCyclic (pCore 3 D))
  | two (model : Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup D, ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty ((D ⧸ N) ≃* E4))
  | three (data : ProductRow S) (sylow : Nonempty (S ≃* DihedralGroup 4))
      (left : Nonempty (G₁ ≃* DihedralGroup 12))
      (right : Nonempty (G₂ ≃* Equiv.Perm (Fin 4)))
  | four (field : FieldParameter.{u}) (degree : field.degree = 1)
      (congruence : field.prime % 24 = 11 ∨ field.prime % 24 = 13)
      (model : D ≃* PSL(2,field.Carrier))
      (component : generalizedFitting D = ⊤)
      (quasisimple : IsQuasisimple (generalizedFitting D))
      (sylow : Nonempty (S ≃* E4))
      (left : Nonempty (G₁ ≃* DihedralGroup 6))
      (right : Nonempty (G₂ ≃* DihedralGroup 6))
  | five (field : FieldParameter.{u}) (degree : field.degree = 1)
      (congruence : field.prime % 24 = 11 ∨ field.prime % 24 = 13)
      (model : D ≃* PGL2 field.Carrier)
      (component : generalizedFitting D ≃* PSL(2,field.Carrier))
      (quasisimple : IsQuasisimple (generalizedFitting D))
      (sylow : Nonempty (S ≃* DihedralGroup 4))
      (left : Nonempty (G₁ ≃* DihedralGroup 12))
      (right : Nonempty (G₂ ≃* Equiv.Perm (Fin 4)))
  | six (model : TripleAlternating D 6 ∨
      ∃ field : FieldParameter.{u}, field.degree ≤ 2 ∧
        (Nat.card field.Carrier % 16 = 7 ∨ Nat.card field.Carrier % 16 = 9) ∧
        Nonempty (D ≃* PSL(2,field.Carrier)))
      (component : generalizedFitting D = ⊤)
      (quasisimple : IsQuasisimple (generalizedFitting D))
      (sylow : Nonempty (S ≃* DihedralGroup 4))
      (left : Nonempty (G₁ ≃* Equiv.Perm (Fin 4)))
      (right : Nonempty (G₂ ≃* Equiv.Perm (Fin 4)))
  | seven (model : Nonempty (D ≃* alternatingGroup (Fin 7)) ∨ TripleAlternating D 7)
      (quasisimple : IsQuasisimple (generalizedFitting D))
      (sylow : Nonempty (S ≃* DihedralGroup 4))
      (left : Nonempty (G₁ ≃* Equiv.Perm (Fin 4)))
      (right : Extension G₂ (C 3 × E4) (C 2))
  | eight (model : Nonempty (TripleSymmetric D 6) ∨ Nonempty (FieldExtensionRow (D := D)))
      (quasisimple : IsQuasisimple (generalizedFitting D))
      (sylow : Nonempty (S ≃* (C 2 × DihedralGroup 4)))
      (left : Nonempty (G₁ ≃* (C 2 × Equiv.Perm (Fin 4))))
      (right : Nonempty (G₂ ≃* (C 2 × Equiv.Perm (Fin 4))))
  | nine (model : Nonempty (D ≃* Equiv.Perm (Fin 7)) ∨ Nonempty (TripleSymmetric D 7))
      (quasisimple : IsQuasisimple (generalizedFitting D))
      (sylow : Nonempty (S ≃* (C 2 × DihedralGroup 4)))
      (left : Nonempty (G₁ ≃* (C 2 × Equiv.Perm (Fin 4))))
      (right : Nonempty (G₂ ≃* (Equiv.Perm (Fin 3) × DihedralGroup 4)))
  | ten (prime : ℕ) (prime_isPrime : prime.Prime)
      (congruence : prime % 8 = 3 ∨ prime % 8 = 5)
      (model : DegreeThree prime D)
      (component : generalizedFitting D = ⊤)
      (quasisimple : IsQuasisimple (generalizedFitting D))
      (sylow : Nonempty (S ≃* W32))
      (left : CyclicQuaternionExtension G₁ (Equiv.Perm (Fin 3)))
      (right : Extension G₂ C4Square (Equiv.Perm (Fin 3)))
  | eleven (data : GraphExtensionRow (D := D))
      (quasisimple : IsQuasisimple (generalizedFitting D))
      (sylow : Extension S C4Square E4)
      (left : QuaternionExtension G₁ (Equiv.Perm (Fin 3)))
      (right : Extension G₂ C4Square (DihedralGroup 6))
  | twelve (model : D ≃* Sporadic.Mathieu.M12)
      (quasisimple : IsQuasisimple (generalizedFitting D))
      (sylow : Extension S C4Square E4)
      (left : QuaternionExtension G₁ (Equiv.Perm (Fin 3)))
      (right : Extension G₂ C4Square (DihedralGroup 6))
  | thirteen (model : D ≃* MulAut Sporadic.Mathieu.M12)
      (component : generalizedFitting D ≃* Sporadic.Mathieu.M12)
      (quasisimple : IsQuasisimple (generalizedFitting D))
      (sylow : Extension S C4Square (DihedralGroup 4))
      (left : QuaternionExtension G₁ (DihedralGroup 6))
      (right : ∃ N : Subgroup G₂, ∃ _ : N.Normal,
        Nonempty (N ≃* C4Square) ∧ Extension (G₂ ⧸ N) (C 3 × E4) (C 2))

/-- Full universal F.6.18, allowing the source's interchange of the two
local labels. Both the triple and the O_{3'} quotient witness are mandatory. -/
def ClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (G₁ G₂ : Subgroup D),
    ChapterF.IsGoldschmidtTriple G₁ G₂ → ThreePrimeSQTKQuotient K D →
    ∃ S : Sylow 2 D, G₁ ⊓ G₂ = (S : Subgroup D) ∧
      (Alternative G₁ G₂ S ∨ Alternative G₂ G₁ S)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource

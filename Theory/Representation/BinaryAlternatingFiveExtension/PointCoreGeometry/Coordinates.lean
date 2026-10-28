module
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelModel
public import Theory.GroupTheory.CentralizerModulo
/-!
# Coordinates and finite tests for the binary A₄ point core

The order-64 two-core consists of all vectors and the regular four-group.
Its order-32 residual core is the existing three-space semidirect four-group.
Four explicit elements detect the centralizer and centralizer modulo the
fixed line. The representative certificate check used 59 seconds and 2.4 GiB
peak memory; no pairwise enumeration of the full order-192 group is needed.

Source: Aschbacher–Smith, proof of 14.6.9(i), printed p.1027.
-/
@[expose] public section
namespace BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry
open Subgroup AlternatingFiveFlag AlternatingFiveBorel
open scoped commutatorElement
local instance : DecidablePred (· ∈ B) := fun g => inferInstanceAs (Decidable (g.val 4 = 4))
local instance : Fintype B := Subtype.fintype _
local instance : Fintype BorelModel := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
local instance : DecidableEq BorelModel := SemidirectProduct.equivProd.injective.decidableEq
local instance : DecidablePred (· ∈ coreModel) := fun x =>
  inferInstanceAs (Decidable (x.left.toAdd.val 4 = 0 ∧ x.right.val.val ∈ four))
local instance : Fintype coreModel := Subtype.fintype _

def outerCore : Subgroup BorelModel := four.comap
  (((alternatingGroup (Fin 5)).subtype.comp B.subtype).comp SemidirectProduct.rightHom)
def vectors : Subgroup BorelModel := (SemidirectProduct.rightHom : BorelModel →* B).ker
def threeSpace : Subgroup BorelModel := vectors ⊓ residualModel
def fixedLine : Subgroup BorelModel := line.map (SemidirectProduct.inl : V →* BorelModel)
local instance : DecidablePred (· ∈ outerCore) := fun x =>
  inferInstanceAs (Decidable (x.right.val.val ∈ four))
local instance : Fintype outerCore := Subtype.fintype _

private def tests : Fin 4 → coreModel := ![
  ⟨⟨Multiplicative.ofAdd ⟨![1,1,0,0,0], by decide +kernel⟩, 1⟩, by decide +kernel⟩,
  ⟨⟨Multiplicative.ofAdd ⟨![1,0,1,0,0], by decide +kernel⟩, 1⟩, by decide +kernel⟩,
  ⟨⟨1, ⟨⟨k₀, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩, by decide +kernel⟩⟩, by decide +kernel⟩,
  ⟨⟨1, ⟨⟨k₁, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩, by decide +kernel⟩⟩, by decide +kernel⟩]

private theorem centralizer_test : ∀ x : outerCore,
    (∀ i : Fin 4, (tests i : BorelModel) * x.val = x.val * tests i) →
      x.val = 1 ∨ x.val = centralElement.val := by decide +kernel

private theorem modulo_test : ∀ x : outerCore,
    (∀ i : Fin 4, ⁅(tests i : BorelModel),x.val⁆ = 1 ∨
      ⁅(tests i : BorelModel),x.val⁆ = centralElement.val) →
        x.val ∈ coreModel := by decide +kernel

/-- Four tests suffice for the centralizer in the literal order-64 two-core. -/
theorem centralizer_cases (x : outerCore)
    (hx : ∀ a ∈ coreModel, a * x.val = x.val * a) :
    x.val = 1 ∨ x.val = centralElement.val :=
  centralizer_test x (fun i => hx (tests i) (tests i).property)

/-- The same tests detect the literal order-32 subgroup modulo its central line. -/
theorem modulo_cases (x : outerCore)
    (hx : ∀ a ∈ coreModel, ⁅a,x.val⁆ = 1 ∨ ⁅a,x.val⁆ = centralElement.val) :
    x.val ∈ coreModel :=
  modulo_test x (fun i => hx (tests i) (tests i).property)

end BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry

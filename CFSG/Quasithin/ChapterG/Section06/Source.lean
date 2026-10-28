module

public import CFSG.Quasithin.Defs
public import Theory.Representation.NormalClosureDisplacement
public import Theory.Representation.BinaryPermutation

/-!
# Source hypotheses and marked models for G.6

These are inputs and conclusions, not classification theorems. Every natural
or permutation-core assertion retains the actor isomorphism and an intertwining
linear equivalence. The two-factor conclusion uses the literal commutator
subspaces and the actual ambient conjugation, with normality relative to K.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.6.1 and G.6.4, printed pp.345–346 (PDF pp.356–357).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section06
open Subgroup Representation.BinaryOffender
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual quotient presentation and all of G.6.1's assumptions. -/
structure Hypotheses (κ : GroupClass.{u}) (ρ : Representation (ZMod 2) G V)
    (a : G) {Cover : Type u} [Group Cover] (q : Cover →* G) : Prop where
  finite_group : Finite G
  finite_cover : Finite Cover
  finite_displacement : Module.Finite (ZMod 2) (LinearMap.range (ρ a - LinearMap.id))
  cover_sqtk : IsSQTK κ Cover
  quotient_surjective : Function.Surjective q
  twoCore : pCore 2 G = ⊥
  faithful : Function.Injective ρ
  involution : a ^ 2 = 1
  nonidentity : a ≠ 1
  displacement_rank : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2
  generated : conjugateDisplacementSpan ρ a ⊤ = ⊤

/-- The rank bound in G.6.1 and the finite orbit already imply finiteness of V. -/
theorem Hypotheses.finite_module {κ : GroupClass.{u}}
    {ρ : Representation (ZMod 2) G V} {a : G}
    {Cover : Type u} [Group Cover] {q : Cover →* G}
    (h : Hypotheses κ ρ a q) : Module.Finite (ZMod 2) V := by
  let := h.finite_group
  let := h.finite_displacement
  exact finite_of_conjugateDisplacementSpan_eq_top ρ a h.generated

/-- The natural representation of GL(n,2) = L_n(2). -/
def binaryLinearAction (n : ℕ) : Representation (ZMod 2)
    ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (Fin n → ZMod 2) where
  toFun g := g.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- A marked model on a specified subspace, for the specified subgroup. -/
def HasModelOn (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (W : Submodule (ZMod 2) V) {B F : Type*} [Group B] [AddCommGroup F]
    [Module (ZMod 2) F] (σ : Representation (ZMod 2) B F) : Prop :=
  ∃ (eK : K ≃* B) (eW : W ≃ₗ[ZMod 2] F)
    (stable : ∀ (k : K) (w : W), ρ k w ∈ W),
    ∀ (k : K) (w : W), eW ⟨ρ k w, stable k w⟩ = σ (eK k) (eW w)

/-- The three alternatives of G.6.4(2), with every parameter restriction. -/
def FactorModel (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (W : Submodule (ZMod 2) V) : Prop :=
  (∃ n, 2 ≤ n ∧ n ≤ 5 ∧ HasModelOn ρ K W (binaryLinearAction n)) ∨
  (∃ n, 5 ≤ n ∧ n ≤ 8 ∧
    HasModelOn ρ K W (BinaryPermutation.naturalRepresentation (Fin n))) ∨
  (∃ n, (n = 6 ∨ n = 8) ∧
    HasModelOn ρ K W (BinaryPermutation.coreRepresentation (Fin n)))

/-- The smaller list permitted for the two factors in G.6.4(3)(ii). -/
def SmallFactorModel (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (W : Submodule (ZMod 2) V) : Prop :=
  HasModelOn ρ K W (binaryLinearAction 2) ∨
  HasModelOn ρ K W (binaryLinearAction 3) ∨
  HasModelOn ρ K W (BinaryPermutation.naturalRepresentation (Fin 5))

/-- Clauses (1)–(3) with a single factor. -/
def OneFactor (ρ : Representation (ZMod 2) G V) (a : G) : Prop :=
  normalClosure ({a} : Set G) = ⊤ ∧
  FactorModel ρ ⊤ (subspaceCommutator ρ ⊤ ⊤) ∧ subspaceCommutator ρ ⊤ ⊤ = ⊤

/-- The two-factor module output, before the ambient normalizer calculation. -/
structure TwoFactorModules (ρ : Representation (ZMod 2) G V) (a : G) where
  first : Subgroup G
  second : Subgroup G
  join_eq : first ⊔ second = normalClosure ({a} : Set G)
  disjoint : first ⊓ second = ⊥
  commute : ⁅first, second⁆ = ⊥
  marked : a ∈ first
  second_nontrivial : second ≠ ⊥
  first_model : SmallFactorModel ρ first (subspaceCommutator ρ ⊤ first)
  second_model : SmallFactorModel ρ second (subspaceCommutator ρ ⊤ second)
  space_sum : subspaceCommutator ρ ⊤ first ⊔ subspaceCommutator ρ ⊤ second = ⊤
  cross_first : subspaceCommutator ρ (subspaceCommutator ρ ⊤ second) first = ⊥
  cross_second : subspaceCommutator ρ (subspaceCommutator ρ ⊤ first) second = ⊥
  permutation : ∀ g : G,
    (first.map (MulAut.conj g).toMonoidHom = first ∧
      second.map (MulAut.conj g).toMonoidHom = second) ∨
    (first.map (MulAut.conj g).toMonoidHom = second ∧
      second.map (MulAut.conj g).toMonoidHom = first)

/-- The classified normal closure, before controlling its ambient overgroup. -/
def ClassifiedClosure (ρ : Representation (ZMod 2) G V) (a : G) : Prop :=
  FactorModel ρ (normalClosure ({a} : Set G)) ⊤ ∨ Nonempty (TwoFactorModules ρ a)

/-- Clauses (1)–(3) in the two-factor case, including the involutory extension. -/
structure TwoFactors (ρ : Representation (ZMod 2) G V) (a : G)
    extends TwoFactorModules ρ a where
  extension : ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧
    normalClosure ({a} : Set G) ⊔ zpowers t = ⊤ ∧
    first.map (MulAut.conj t).toMonoidHom = second

/-- The 2-central list, including both allowed S₆ modules. -/
def CentralModel (ρ : Representation (ZMod 2) G V) : Prop :=
  (∃ n, 2 ≤ n ∧ n ≤ 5 ∧ HasModelOn ρ ⊤ ⊤ (binaryLinearAction n)) ∨
  HasModelOn ρ ⊤ ⊤ (BinaryPermutation.naturalRepresentation (Fin 6)) ∨
  HasModelOn ρ ⊤ ⊤ (BinaryPermutation.naturalRepresentation (Fin 7)) ∨
  HasModelOn ρ ⊤ ⊤ (BinaryPermutation.coreRepresentation (Fin 6))

/-- The complete conclusion of G.6.4. Its proof remains an assembly obligation. -/
def Conclusion (ρ : Representation (ZMod 2) G V) (a : G) : Prop :=
  (OneFactor ρ a ∨ Nonempty (TwoFactors ρ a)) ∧
  (∀ T : Sylow 2 G, a ∈ (center T).map (T : Subgroup G).subtype →
    normalClosure ({a} : Set G) = ⊤ ∧ CentralModel ρ)
end CFSG.Quasithin.ChapterG.Section06

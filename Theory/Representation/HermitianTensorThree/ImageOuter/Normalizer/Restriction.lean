module
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Representation
public import Theory.Representation.BinaryOffender.CentralSectionAction

/-!
# The diagram obstruction on a restricted actor

The diagram actor and the normal component can be restricted to any
subgroup containing them. Every representation of that subgroup then
inherits the Hermitian obstruction. This applies in particular to
invariant subspaces and their central quotients, without identifying
them with the original ambient module.

Source application: Aschbacher--Smith 5.1.23, printed p.646.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
open Representation.HermitianTensorThree
open Matrix.PSL3.LinearThree.OuterExtensions
namespace Representation.HermitianTensorThree.ImageOuter
open Representation.BinaryOffender
variable {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]

/-- Retain the same component marking and implementing element in a smaller actor. -/
theorem not_hermitian_on_subgroup
    (K J : Subgroup X) (hKJ : K ≤ J)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : K ≃* PSL(3,F)) (t : X) (ht : t ∈ J)
    (a : MulAut K) (b : MulAut PSL(3,F))
    (ha : ∀ k : K, (a k : X) = t * k * t⁻¹)
    (hb : ∀ k, e (a k) = b (e k)) (hd : b ∉ diagramTrivial F)
    (σ : Representation (ZMod 2) J W) :
    ¬ ∃ (j : K ≃* PSL(3,E 1)) (c : W ≃ₗ[ZMod 2] Space 1),
      ∀ k : K, ∀ w : W,
        c (σ (inclusion hKJ k) w) = projectiveAction (j k) (c w) := by
  let q : K.subgroupOf J ≃* K := subgroupOfEquivOfLe hKJ
  let a' := MulAut.congr q.symm a
  have ha' (k : K.subgroupOf J) :
      (a' k : J) = (⟨t,ht⟩ : J) * k * (⟨t,ht⟩ : J)⁻¹ := by
    apply Subtype.ext
    exact ha (q k)
  have hb' (k : K.subgroupOf J) :
      (q.trans e) (a' k) = b ((q.trans e) k) := by
    change e (q (q.symm (a (q k)))) = b (e (q k))
    rw [q.apply_symm_apply]
    exact hb (q k)
  rintro ⟨j,c,hc⟩
  apply not_hermitian_of_diagram_action σ (K.subgroupOf J) hF
    (q.trans e) ⟨t,ht⟩ a' b ha' hb' hd
  exact ⟨q.trans j,c,fun k w => hc (q k) w⟩

/-- The Hermitian row is excluded on every invariant central section for this join. -/
@[expose] def NoHermitianCentralSections (ρ : Representation (ZMod 2) X W)
    (K P : Subgroup X) : Prop :=
  ∀ (U : Submodule (ZMod 2) W) (hU : K ⊔ P ≤ subspaceStabilizer ρ U)
    (hN : K ⊔ P ≤ normalizer (K : Set X)),
    ¬ ∃ (j : K ≃* PSL(3,E 1)) (c : centralQuotient ρ K U ≃ₗ[ZMod 2] Space 1),
      ∀ k : K, ∀ w,
        c (centralSectionRepresentation ρ K (K ⊔ P) U hU hN
          (inclusion (show K ≤ K ⊔ P from le_sup_left) k) w) = projectiveAction (j k) (c w)

/-- The original diagram element supplies the obstruction for all such quotients. -/
theorem noHermitianCentralSections_of_diagram
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : K ≃* PSL(3,F)) (t : X) (ht : t ∈ P)
    (a : MulAut K) (b : MulAut PSL(3,F))
    (ha : ∀ k : K, (a k : X) = t * k * t⁻¹)
    (hb : ∀ k, e (a k) = b (e k)) (hd : b ∉ diagramTrivial F) :
    NoHermitianCentralSections ρ K P := by
  intro U hU hN
  exact not_hermitian_on_subgroup K (K ⊔ P) le_sup_left hF e t (mem_sup_right ht)
    a b ha hb hd (centralSectionRepresentation ρ K (K ⊔ P) U hU hN)

end Representation.HermitianTensorThree.ImageOuter

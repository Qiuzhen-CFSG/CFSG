module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.LocalGeneration
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Equivariant transport of a cyclic-source generation witness

An equivariant identification of both actor and whole binary module transports
D.2.17's literal odd kernel, marked involution, generation, commutator,
full movement and fixed codimension. The proof maps the group identities and
uses the existing equivariant commutator and fixed-space identities.

Source: Aschbacher--Smith D.2.17, used in 15.1.2's singleton cyclic case,
printed p.1086.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}
  [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]

/-- Transport the literal odd kernel and generator through equivariant
identifications of the actor and the whole module. -/
@[expose] def LocalGeneration.mapEquiv (l : LocalGeneration ρ) (e : G ≃* H)
    (x : V ≃ₗ[ZMod 2] W) (hx : ∀ g v, x (ρ g v) = σ (e g) (x v)) :
    LocalGeneration σ where
  kernel := l.kernel.map e.toMonoidHom
  normal := l.normal.map e.toMonoidHom e.surjective
  prime := l.prime
  prime_prime := l.prime_prime
  prime_odd := l.prime_odd
  pgroup := l.pgroup.map e.toMonoidHom
  nontrivial := by
    intro hh
    apply l.nontrivial
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_bot] using hh
  involution := e l.involution
  order_two := (e.orderOf_eq l.involution).trans l.order_two
  generated := by
    have hz : (zpowers l.involution).map e.toMonoidHom = zpowers (e l.involution) :=
      e.toMonoidHom.map_zpowers l.involution
    have hh := congrArg (fun A : Subgroup G => A.map e.toMonoidHom) l.generated
    rw [Subgroup.map_sup,hz,Subgroup.map_top_of_surjective _ e.surjective] at hh
    exact hh
  commutator := by
    have hz : (zpowers l.involution).map e.toMonoidHom = zpowers (e l.involution) :=
      e.toMonoidHom.map_zpowers l.involution
    have hh := congrArg (fun A : Subgroup G => A.map e.toMonoidHom) l.commutator
    rw [Subgroup.map_commutator,hz] at hh
    exact hh
  moved := by
    have hxi : ∀ g w, ρ g (x.symm w) = x.symm (σ (e g) w) := by
      intro g w
      apply x.injective
      simpa only [x.apply_symm_apply] using hx g (x.symm w)
    have hh := subspaceCommutator_map_embedding ρ σ e.toMonoidHom x.symm.toLinearMap
      hxi l.kernel ⊤
    have ht : (⊤ : Submodule (ZMod 2) W).map x.symm.toLinearMap = ⊤ :=
      by rw [Submodule.map_top,LinearEquiv.range]
    rw [ht,l.moved] at hh
    apply Submodule.map_injective_of_injective x.symm.injective
    exact hh.symm.trans ht.symm
  codimension := by
    have hh := fixedCodim_map_equivariant ρ σ e.toMonoidHom x hx (zpowers l.involution)
    rw [MonoidHom.map_zpowers] at hh
    exact hh ▸ l.codimension
end CFSG.Quasithin.ChapterD.CyclicSource


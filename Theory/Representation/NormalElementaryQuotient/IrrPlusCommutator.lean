module

public import Theory.Representation.BinaryOffender.NoncentralMoved
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.NormalElementaryEmbedding
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# Faithful elementary inclusions preserve an Irr-plus commutator

For a perfect actor, every noncentral invariant subspace has the full moved
space when that moved space lies in Irr-plus. A faithful elementary subgroup
inside another faithful elementary subgroup is noncentral under their common
literal quotient action. Equivariant inclusion and commutator coordinates
therefore identify their actual ambient subgroup commutators.

Source application: Meierfrankenfeld--Stellmacher (1993), the initial moved
layer in (3.2)(vi), [X,L]=U.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {H J : Type*} [Group H] [Group J]

/-- A faithful elementary submodule has the same actual commutator as its
containing module when the latter has an Irr⁺ moved space. -/
theorem commutator_eq_of_irrPlus
    (W X : Subgroup H) [W.Normal] [X.Normal]
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 X]
    (hWX : W ≤ X) (q : H →* J) (hq : Function.Surjective q)
    (hW : q.ker = centralizer (W : Set H))
    (hX : q.ker = centralizer (X : Set H))
    (K : Subgroup H) (C : Subgroup J) [Group.IsPerfect C]
    (hKC : K.map q = C) (hne : C ≠ ⊥)
    (hi : IsIrrPlus (NormalElementaryQuotient.representation X q hq hX) C
      (subspaceCommutator (NormalElementaryQuotient.representation X q hq hX) ⊤ C)) :
    ⁅W,K⁆ = ⁅X,K⁆ := by
  let ρ := NormalElementaryQuotient.representation X q hq hX
  let σ := NormalElementaryQuotient.representation W q hq hW
  let e := NormalElementaryQuotient.inclusionLinear W X hWX
  have he : Function.Injective e := NormalElementaryQuotient.inclusionLinear_injective W X hWX
  have hact : ∀ g w, e (σ g w) = ρ g (e w) :=
    NormalElementaryQuotient.inclusionLinear_intertwines W X hWX q hq hW hX
  have hn : ¬ LinearMap.range e ≤ fixedSpace ρ C :=
    range_not_fixed_of_faithful_embedding ρ σ e he hact
      (NormalElementaryQuotient.representation_injective W q hq hW) C hne
  have hs : C ≤ subspaceStabilizer ρ (LinearMap.range e) := by
    apply le_subspaceStabilizer
    rintro c hc _ ⟨w,rfl⟩
    exact ⟨σ c w,hact c w⟩
  have heq := moved_eq_of_noncentral_invariant ρ C hi (LinearMap.range e) hs hn
  have hm : (subspaceCommutator σ ⊤ C).map e = subspaceCommutator ρ ⊤ C := by
    have hh := subspaceCommutator_map_embedding ρ σ (MonoidHom.id J) e
      (fun g w => (hact g w).symm) C ⊤
    simpa only [Submodule.map_top,Subgroup.map_id,heq] using hh.symm
  apply le_antisymm (commutator_mono hWX le_rfl)
  intro x hx
  let v : Additive X := Additive.ofMul ⟨x,(commutator_le_left X K) hx⟩
  have hv : v ∈ subspaceCommutator ρ ⊤ C := by
    rw [← hKC, ← NormalElementaryQuotient.commutatorSpace_eq X q hq hX]
    exact hx
  rw [← hm] at hv
  obtain ⟨w,hw,hew⟩ := hv
  have hw' : (w.toMul : H) ∈ ⁅W,K⁆ := by
    rw [← hKC, ← NormalElementaryQuotient.commutatorSpace_eq W q hq hW] at hw
    exact hw
  have hex : (w.toMul : H) = x :=
    congrArg (fun z : Additive X => (z.toMul : H)) hew
  exact hex ▸ hw'

end Representation.NormalElementaryQuotient

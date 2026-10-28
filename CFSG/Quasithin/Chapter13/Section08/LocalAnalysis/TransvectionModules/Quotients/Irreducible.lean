module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Sections
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.Order.Atoms.Finite

/-!
# Local planes in the irreducible quotient used by 13.8.6(4)

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed p.948, the application of G.5.2.

A local irreducible submodule whose full-group orbit spans the module
survives injectively in every proper invariant quotient: otherwise the
kernel contains every conjugate and hence the whole module. We construct
the actual local intertwining map and its equivalence onto its image.
A maximal invariant subspace then gives an irreducible quotient in which
both prescribed local planes survive, preserving their actions and ranks.

The identification of these local modules with U_H V/V and U₂/V from the
source setup, and the subsequent recognition as Steinberg, are separate
obligations. No dimension alone identifies a representation here.
-/

@[expose] public section

open Subgroup Representation Module
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients
variable {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
variable (ρ : Representation (ZMod 2) A X)

/-- Restrict the literal quotient projection to a local invariant subspace. -/
def localQuotientMap (P : Subgroup A) (S : Subrepresentation (ρ.comp P.subtype))
    (W : Subrepresentation ρ) :
    Representation.IntertwiningMap S.toRepresentation (W.quotientRepresentation.comp P.subtype) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (W.toSubmodule.mkQ.comp S.toSubmodule.subtype) (by intro p s; rfl)

/-- Irreducibility and full orbit generation prevent the local module being killed. -/
theorem localQuotientMap_injective (P : Subgroup A)
    (S : Subrepresentation (ρ.comp P.subtype)) [Representation.IsIrreducible S.toRepresentation]
    (hgen : Submodule.span (ZMod 2) {x | ∃ a : A, ∃ s : S, x = ρ a (s : X)} = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) :
    Function.Injective (localQuotientMap ρ P S W) := by
  apply (Representation.IsIrreducible.injective_or_eq_zero (localQuotientMap ρ P S W)).resolve_right
  intro hz
  have hSW (s : S) : (s : X) ∈ W := by
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
    exact DFunLike.congr_fun hz s
  have htop : (⊤ : Submodule (ZMod 2) X) ≤ W.toSubmodule := by
    rw [← hgen]
    apply Submodule.span_le.mpr
    rintro x ⟨a, s, rfl⟩
    exact W.apply_mem_toSubmodule a (hSW s)
  exact hW (Subrepresentation.toSubmodule_injective (top_unique htop))

/-- The surviving local module is equivariantly isomorphic to its actual image. -/
noncomputable def localQuotientEquiv (P : Subgroup A)
    (S : Subrepresentation (ρ.comp P.subtype)) [Representation.IsIrreducible S.toRepresentation]
    (hgen : Submodule.span (ZMod 2) {x | ∃ a : A, ∃ s : S, x = ρ a (s : X)} = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) :
    S.toRepresentation.Equiv (localQuotientMap ρ P S W).range.toRepresentation := by
  let q := localQuotientMap ρ P S W
  let e := LinearEquiv.ofInjective q.toLinearMap (localQuotientMap_injective ρ P S hgen W hW)
  refine Representation.Equiv.mk e ?_
  intro p
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  exact IntertwiningMap.isIntertwining _ _ q p s

/-- A local plane remains a plane in every proper invariant quotient. -/
theorem localQuotientMap_finrank (P : Subgroup A)
    (S : Subrepresentation (ρ.comp P.subtype)) [Representation.IsIrreducible S.toRepresentation]
    (hgen : Submodule.span (ZMod 2) {x | ∃ a : A, ∃ s : S, x = ρ a (s : X)} = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (hdim : Module.finrank (ZMod 2) S.toSubmodule = 2) :
    Module.finrank (ZMod 2) (localQuotientMap ρ P S W).range.toSubmodule = 2 := by
  rw [← (localQuotientEquiv ρ P S hgen W hW).toLinearEquiv.finrank_eq]
  exact hdim

private theorem irreducible_quotient_of_coatom
    (W : Subrepresentation ρ) (hW : IsCoatom W) : W.quotientRepresentation.IsIrreducible := by
  have hn : W.toSubmodule ≠ ⊤ := fun he => hW.1 (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial (X ⧸ W.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hn
  refine ⟨?_⟩
  intro S
  let T : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule.comap W.toSubmodule.mkQ
    apply_mem_toSubmodule a x hx := S.apply_mem_toSubmodule a hx
  }
  have hWT : W ≤ T := by
    intro x hx
    change W.toSubmodule.mkQ x ∈ S
    have hz : W.toSubmodule.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
    rw [hz]
    exact S.toSubmodule.zero_mem
  rcases eq_or_lt_of_le hWT with he | hlt
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro w hw
    obtain ⟨x, rfl⟩ := W.toSubmodule.mkQ_surjective w
    exact (Submodule.Quotient.mk_eq_zero _).mpr (show x ∈ W from he.symm ▸ hw)
  · right
    have ht : T = ⊤ := hW.2 T hlt
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    obtain ⟨x, rfl⟩ := W.toSubmodule.mkQ_surjective w
    exact (show x ∈ T from ht.symm ▸ (show x ∈ (⊤ : Subrepresentation ρ) from by trivial))

/-- A nonzero finite binary module has a genuine irreducible quotient. -/
theorem exists_irreducible_quotient [Finite X] [Nontrivial X] :
    ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧ W.quotientRepresentation.IsIrreducible := by
  let : Finite (Subrepresentation ρ) :=
    Finite.of_injective (fun W : Subrepresentation ρ => (W : Set X)) SetLike.coe_injective
  obtain ⟨W, hW⟩ := IsCoatomic.exists_coatom (Subrepresentation ρ)
  exact ⟨W, hW.1, irreducible_quotient_of_coatom ρ W hW⟩

/-- Both local planes survive in one irreducible quotient, as needed for G.5.2. -/
theorem exists_irreducible_quotient_with_local_planes [Finite X] [Nontrivial X]
    (P₁ P₂ : Subgroup A)
    (S₁ : Subrepresentation (ρ.comp P₁.subtype))
    (S₂ : Subrepresentation (ρ.comp P₂.subtype))
    [Representation.IsIrreducible S₁.toRepresentation]
    [Representation.IsIrreducible S₂.toRepresentation]
    (hgen₁ : Submodule.span (ZMod 2) {x | ∃ a : A, ∃ s : S₁, x = ρ a (s : X)} = ⊤)
    (hgen₂ : Submodule.span (ZMod 2) {x | ∃ a : A, ∃ s : S₂, x = ρ a (s : X)} = ⊤)
    (hdim₁ : Module.finrank (ZMod 2) S₁.toSubmodule = 2)
    (hdim₂ : Module.finrank (ZMod 2) S₂.toSubmodule = 2) :
    ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧ W.quotientRepresentation.IsIrreducible ∧
      Nonempty (S₁.toRepresentation.Equiv (localQuotientMap ρ P₁ S₁ W).range.toRepresentation) ∧
      Nonempty (S₂.toRepresentation.Equiv (localQuotientMap ρ P₂ S₂ W).range.toRepresentation) ∧
      Module.finrank (ZMod 2) (localQuotientMap ρ P₁ S₁ W).range.toSubmodule = 2 ∧
      Module.finrank (ZMod 2) (localQuotientMap ρ P₂ S₂ W).range.toSubmodule = 2 := by
  obtain ⟨W, hW, hi⟩ := exists_irreducible_quotient ρ
  exact ⟨W, hW, hi,
    ⟨localQuotientEquiv ρ P₁ S₁ hgen₁ W hW⟩,
    ⟨localQuotientEquiv ρ P₂ S₂ hgen₂ W hW⟩,
    localQuotientMap_finrank ρ P₁ S₁ hgen₁ W hW hdim₁,
    localQuotientMap_finrank ρ P₂ S₂ hgen₂ W hW hdim₂⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients

end

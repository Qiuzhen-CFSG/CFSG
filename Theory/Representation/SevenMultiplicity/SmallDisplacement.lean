module
public import Theory.Representation.PerfectInvolutionExtension
public import Theory.Representation.NormalInvariants

/-!
# Irreducible restriction under a small-displacement generator

A simple normal subgroup surviving on an irreducible representation acts
faithfully on every simple constituent. If it and one element generate the
actor, and that element moves fewer dimensions than a constituent, the
normal-constituent displacement lemma makes the constituent invariant under
the whole actor. Thus restriction is irreducible.

This is the constituent-stabilizer step in Aschbacher–Smith 5.1.17, p.641
(refs/quasithin.pdf). The L3Four SevenProduct extension applies it at the
literal nine-dimensional threshold.
-/

public noncomputable section

open Subgroup Representation
namespace Representation.SevenMultiplicity
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A simple normal subgroup which survives on an irreducible module acts faithfully
on each of its simple constituents. -/
theorem simple_constituent_faithful (ρ : Representation k G V)
    (hi : IsIrreducible ρ) (K : Subgroup G) [K.Normal] [IsSimpleGroup K]
    (hn : ¬ K ≤ ρ.ker)
    (J : Subrepresentation (ρ.comp K.subtype)) (hJ : IsIrreducible J.toRepresentation) :
    Function.Injective J.toRepresentation := by
  rcases (inferInstance : J.toRepresentation.ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact (MonoidHom.ker_eq_bot_iff _).mp hk
  exfalso
  apply hn
  let := hi
  apply le_ker_of_normal_invariants_ne_bot ρ K
  intro hz
  have hle : J.toSubmodule ≤ invariants (ρ.comp K.subtype) := by
    intro v hv k
    have hmem : k ∈ J.toRepresentation.ker := by rw [hk]; trivial
    exact congrArg Subtype.val (LinearMap.congr_fun hmem (⟨v,hv⟩ : J.toSubmodule))
  have hbot : J.toSubmodule = ⊥ := bot_unique (hle.trans hz.le)
  exact ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot
    (Subrepresentation.toSubmodule_injective hbot)

end Representation.SevenMultiplicity
namespace Representation.SevenMultiplicity
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
/-- If a normal subgroup and a small-displacement element generate the actor,
restriction is irreducible whenever each simple constituent is larger than
the element's displacement. -/
theorem restriction_irreducible_of_small_displacement (ρ : Representation (ZMod 2) G V)
    (hi : IsIrreducible ρ) (K : Subgroup G) [K.Normal]
    (y : G) (hgen : K ⊔ zpowers y = ⊤)
    (hsmall : ∀ J : Subrepresentation (ρ.comp K.subtype),
      IsIrreducible J.toRepresentation →
      Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) < Module.finrank (ZMod 2) J.toSubmodule) :
    IsIrreducible (ρ.comp K.subtype) := by
  let := hi
  let := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J,hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp K.subtype)
  have hstable : J.toSubmodule.map (ρ y) = J.toSubmodule :=
    map_constituent_eq_self_of_displacement_lt ρ K y J hJ (hsmall J hJ)
  have hK : K ≤ BinaryOffender.subspaceStabilizer ρ J.toSubmodule :=
    BinaryOffender.le_subspaceStabilizer ρ J.toSubmodule
      (fun k hk w hw => J.apply_mem_toSubmodule ⟨k,hk⟩ hw)
  have hy : y ∈ BinaryOffender.subspaceStabilizer ρ J.toSubmodule := by
    intro w
    constructor
    · intro hw
      obtain ⟨x,hx,he⟩ := hstable.ge hw
      exact (ρ.apply_bijective y).injective he ▸ hx
    · intro hw
      exact hstable.le (Submodule.mem_map_of_mem hw)
  have hall : ⊤ ≤ BinaryOffender.subspaceStabilizer ρ J.toSubmodule :=
    hgen ▸ sup_le hK (zpowers_le.mpr hy)
  let P : Subrepresentation ρ := {
    toSubmodule := J.toSubmodule
    apply_mem_toSubmodule g w hw := (hall (mem_top g) w).mpr hw }
  have hP : P ≠ ⊥ := fun he =>
    ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot
      (Subrepresentation.toSubmodule_injective (congrArg (fun Q : Subrepresentation ρ => Q.toSubmodule) he))
  have ht : P = ⊤ := (hi.eq_bot_or_eq_top P).resolve_left hP
  have hJtop : J = ⊤ := Subrepresentation.toSubmodule_injective
    (congrArg (fun Q : Subrepresentation ρ => Q.toSubmodule) ht)
  exact isSimpleOrder_iff_isAtom_top.mpr
    (hJtop ▸ (Subrepresentation.irreducible_iff_isAtom J).mp hJ)
end Representation.SevenMultiplicity

module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix.Coordinates
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix.PermutationFactors
public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.Representation.FactorMapFiltration

/-!
# Recognizing the binary degree-six G₂(2)′ action from concrete factor maps

A transitive permutation action with two-group stabilizer surjects onto every
irreducible binary representation. A finite filtration of that permutation
module, with nonzero maps from each degree-six simple factor to the actual
natural coordinate action, therefore recognizes its degree-six irreducible
quotients. The coordinate equivalence returns the precise trace-zero octonion
quotient action used in G.9.3(10), with an actual intertwining linear equivalence.

The concrete flag action has a two-group stabilizer, and `PermutationFactors`
supplies the required filtration and maps. Thus `quasiequivalent_of_finrank_eq_six`
recognizes every six-dimensional irreducible binary action of the actual derived
group, in particular every faithful such action, without additional premises.

Source: Aschbacher--Smith G.9.3(10), printed pp.354,356--357. The group throughout
is `commutator (Atlas.G2.Model (ZMod 2))`, including the binary exception.
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix

attribute [local instance] scalars

open Atlas.G2.Natural.Binary

/-- Recognition from concrete simple-factor maps, retaining the entire actual
commutator-group action. The concrete flag filtration is supplied in
`quasiequivalent_of_finrank_eq_six` below. -/
theorem quasiequivalent_of_permutation_factor_maps
    {Ω V : Type*} [Fintype Ω] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (τ : Derived →* Equiv.Perm Ω) (o : Ω)
    (H : Subgroup Derived) (hH : IsPGroup 2 H)
    (hstab : ∀ g : Derived, g ∈ H ↔ τ g o = o)
    (htrans : ∀ x : Ω, ∃ g : Derived, τ g o = x)
    (hfiltration : Representation.FactorMapFiltration coordinateAction
      ((BinaryPermutation.representation Ω).comp τ))
    (ρ : Representation (ZMod 2) Derived V) [Representation.IsIrreducible ρ]
    (hd : Module.finrank (ZMod 2) V = 6) :
    Quasiequivalent ρ (derivedNaturalBinary (ZMod 2)) := by
  obtain ⟨e⟩ := BinaryPermutation.equiv_of_factorMapFiltration
    τ o H hH hstab htrans coordinateAction hfiltration ρ (by simpa using hd)
  let f := e.trans BinarySix.coordinateEquiv.symm
  exact ⟨MulEquiv.refl _, f.toLinearEquiv,
    fun g v => Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap g v⟩

/-- Every six-dimensional irreducible binary representation of the actual
G₂(2)′ is quasiequivalent to its natural trace-zero octonion quotient action.
This proves the degree-six recognition step of G.9.3(10) at the binary endpoint;
the argument also applies without a separate faithfulness hypothesis. -/
theorem quasiequivalent_of_finrank_eq_six
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (commutator (Atlas.G2.Model (ZMod 2))) V)
    [Representation.IsIrreducible ρ]
    (hd : Module.finrank (ZMod 2) V = 6) :
    Quasiequivalent ρ (derivedNaturalBinary (ZMod 2)) := by
  exact quasiequivalent_of_permutation_factor_maps
    G2DerivedPermutationFiltration.flagPerm G2DerivedPermutationFiltration.baseFlag
    G2DerivedPermutationFiltration.flagStabilizer
    G2DerivedPermutationFiltration.flagStabilizer_isPGroup
    G2DerivedPermutationFiltration.mem_flagStabilizer_iff
    G2DerivedPermutationFiltration.flagTransitive flag_factorMapFiltration ρ hd

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix

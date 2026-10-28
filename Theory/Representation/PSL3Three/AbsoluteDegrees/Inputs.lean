module

public import Theory.Representation.PSL3Three.SmallDegreeDescent

/-!
# Construction inputs for the PSL₃(3) degree calculation

The two inputs below ask for actual simple representations of the literal
matrix group. They do not assume completeness or put a restriction on an
arbitrary representation. Together with the trivial module these constructions
give seven candidates. A separate bound on odd-order conjugacy classes will
make that family exhaustive.

The degree-26 candidate is used only to saturate the class bound and thereby
exclude further degrees at most eighteen. No higher-degree classification or
field-of-definition assertion is included here.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.2,
manuscript pp.9--10; the characteristic-two decomposition matrix for L₃(3)
lists degrees 1, 12, 26 and four distinct degree-16 simples. These definitions
are outstanding construction contracts, not proofs of that table.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees
universe v

/-- Construct the two nontrivial principal-block candidates. Block membership
is unnecessary for the exhaustion argument and is not part of this contract. -/
@[expose] def PrincipalModelsExist : Prop :=
  ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
    ∃ (ρ₁₂ : Representation F Matrix.PSL3Three.PSL (Fin 12 → F))
      (ρ₂₆ : Representation F Matrix.PSL3Three.PSL (Fin 26 → F)),
      IsIrreducible ρ₁₂ ∧ IsIrreducible ρ₂₆

/-- Construct four inequivalent degree-16 simple modules over each algebraically
closed coefficient field. Actual representations and equivalences are used. -/
@[expose] def SixteenModelsExist : Prop :=
  ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
    ∃ ρ : Fin 4 → Representation F Matrix.PSL3Three.PSL (Fin 16 → F),
      (∀ i, IsIrreducible (ρ i)) ∧
      Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))

end Representation.PSL3Three.AbsoluteDegrees

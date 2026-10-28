module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import Theory.Representation.SymplecticFourOrthogonalCover.ParabolicFixed

/-!
# Central-point exclusion in a natural symplectic cover

An actual proper local C-component with alternating-five two-core quotient
is a conjugate of the point or plane local over the field of order four.
The orthogonal-cover calculation then separates its core-fixed commutator
space from the global fixed space. In particular a fully moved subspace
centralized by its two-core contains no nonzero globally fixed vector.

The natural representation uses the genuine derived carrier; local placement
uses its literal image in the full symplectic matrix group. The quotient
marking is transported along that inclusion before applying placement.

Source: Aschbacher--Smith, 9.4.1, printed p.735/PDF p.752, the Sp₄(4)
branch of the FF-module argument. This discharges the model fixed-space step
with the original local two-core and original natural-cover projection.
-/

public section

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Representation Representation.OneCohomology Representation.BinaryOffender
open Representation.SymplecticFourOrthogonalCover

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := F)) W}

/-- The actual local A₅ section supplies both the field-four parameter and
the conjugate parabolic model for the fixed-space commutator exclusion. -/
theorem symplectic_five_section_cover_moved_disjoint {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) (B : Subgroup (L (K := F)))
    (hB : B.map (commutator (Sp F)).subtype ∈ localCComponents S)
    (hproper : B.map (commutator (Sp F)).subtype ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (A : Submodule (ZMod 2) W) (hA : A ≤ fixedSpace σ (B.pCoreIn 2))
    (hm : subspaceCommutator σ A B = A) : Disjoint A (fixed σ) := by
  let a := B.equivMapOfInjective (commutator (Sp F)).subtype
    (commutator (Sp F)).subtype_injective
  have hk : IsPGroup 2 a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    exact IsPGroup.of_subsingleton 2 _
  let aq := a.toMonoidHom.quotientPCoreEquivOfSurjective a.surjective hk
  obtain ⟨h4,g,hg⟩ := symplectic_five_section_placement hF hn S
    (B.map (commutator (Sp F)).subtype) hB hproper (aq.symm.trans e)
  exact ParabolicFixed.cover_moved_subspace_disjoint h4 p hp B g hg A hA hm

/-- The central point in the original fully moved local subspace is zero. -/
theorem symplectic_five_section_cover_fixed_eq_zero {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) (B : Subgroup (L (K := F)))
    (hB : B.map (commutator (Sp F)).subtype ∈ localCComponents S)
    (hproper : B.map (commutator (Sp F)).subtype ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (A : Submodule (ZMod 2) W) (hA : A ≤ fixedSpace σ (B.pCoreIn 2))
    (hm : subspaceCommutator σ A B = A)
    (v : W) (hv : v ∈ A) (hfixed : v ∈ fixed σ) : v = 0 :=
  Submodule.disjoint_def.mp
    (symplectic_five_section_cover_moved_disjoint hF hn S B hB hproper e p hp A hA hm)
    v hv hfixed

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF

module

public import Theory.SpecificGroups.LinearHigher.TorusAction

/-!
# The torus words for degree-three faithfulness

These are the literal words in the existing Steinberg presentation. The
finite-field argument must establish their multiplicativity, while the
Bruhat argument reduces a matrix-kernel element to the two simple tori.
Neither assertion is assumed as an instance or added to the relators.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, Lemmas 38–40 and
Theorems 8–9, printed pp.71–74 (`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

@[expose] public section

namespace Matrix.PSL3.UniversalProjection.Faithfulness

open Theory.SpecificGroups.LinearHigher SteinbergWords

variable {F : Type*} [Field F]

/-- The standard rank-one torus word, with its nonzero field parameter. -/
abbrev torus (i j : Fin 3) (hij : i ≠ j) (t : Fˣ) : SteinbergGroup 3 F :=
  torusWord generator i j hij t

/-- The centrality required by the finite-field symbol calculation is already
valid in the literal degree-three presentation. -/
theorem torus_defect_mem_center (i j : Fin 3) (hij : i ≠ j) (s t : Fˣ) :
    torus i j hij s * torus i j hij t * (torus i j hij (s * t))⁻¹ ∈
      Subgroup.center (SteinbergGroup 3 F) :=
  torusWord_defect_mem_center (by decide) i j hij s t

/-- Relation (C) from Steinberg §6, to be proved from the defining relations. -/
def TorusMultiplicative (F : Type*) [Field F] : Prop :=
  ∀ (i j : Fin 3) (hij : i ≠ j) (s t : Fˣ),
    torus i j hij s * torus i j hij t = torus i j hij (s * t)

/-- The matrix-kernel conclusion of Bruhat reduction and collection in the
two simple tori. This is a pending mathematical input, not a presentation
relation or a faithfulness assertion. -/
def KernelTorusReduction (F : Type*) [Field F] : Prop :=
  ∀ g : SteinbergGroup 3 F, matrixMap g = 1 →
    ∃ s t : Fˣ, g = torus 0 1 (by decide) s * torus 1 2 (by decide) t

end Matrix.PSL3.UniversalProjection.Faithfulness

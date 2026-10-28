module

public import CFSG.Quasithin.Chapter1.Defs
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Local subgroups in §13.8

These are the actual subgroup constructions on printed pp.946–947 of
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004. They do not assume any of Lemmas 13.8.4–18.

The two denominators in the critical pair are different: `D_H` and `E_H`
centralize `Uγ/A₁`, whereas `Dγ` and `Eγ` centralize `UH/V₁`.
`commutatorPreimage` expresses these conditions without assuming normality
in the ambient simple group. Under the local normalization conditions its
membership means precisely that the indicated commutators lie in the
specified denominator. Its quotient-centralizer theorem may be applied
inside the local overgroup where that denominator is normal.

Conjugate spans use left conjugation. Since the conjugating elements range
over a subgroup, the resulting span agrees with the source convention.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.Source

open Subgroup

variable {G : Type*} [Group G]

/-- The actual family on printed p.946, with nontrivial two-core inherited
from `H(L₁T)`. No minimality is imposed in this definition. -/
def Hz (L₁ T G₁ M : Subgroup G) : Set (Subgroup G) :=
  {H | H ∈ Chapter1.HOver G ((L₁ ⊔ T : Subgroup G) : Set G) ∧ H ≤ G₁ ∧ ¬ H ≤ M}

/-- `U_H = ⟨V₃^H⟩`. -/
def UH (H V₃ : Subgroup G) : Subgroup G := conjugateSpanBy V₃ H

/-- `V_H = ⟨V^H⟩`. -/
def VH (H V : Subgroup G) : Subgroup G := conjugateSpanBy V H

/-- The ambient image of the intrinsic two-core of H. -/
def QH (H : Subgroup G) : Subgroup G := H.pCoreIn 2

/-- The actual quotient `H/O₂(H)`, not an arbitrary faithful actor. -/
abbrev Hstar (H : Subgroup G) := H ⧸ pCore 2 H

/-- The image denoted X* in H*. The intersection with H is explicit in
`subgroupOf`; applications to a source subgroup X supply `X ≤ H`.
In particular K* must not be replaced by K/O₂(K) without identifying the kernel. -/
def starImage (H X : Subgroup G) : Subgroup (Hstar H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))

/-- The source module carrier Ũ_H. A group or module structure on this
quotient requires normality of V₁ inside U_H; no ambient normality is asserted.
Source applications also supply `V₁ ≤ UH H V₃`. -/
abbrev Utilde (H V₃ V₁ : Subgroup G) :=
  UH H V₃ ⧸ V₁.subgroupOf (UH H V₃)

/-- The carrier of V_H/U_H. As with Ũ_H, local normality and containment
are obligations of the source setup, not conclusions of this definition. -/
abbrev Vsection (H V V₃ : Subgroup G) :=
  VH H V ⧸ (UH H V₃).subgroupOf (VH H V)

/-- `H_C = C_H(U_H)`. -/
def HC (H V₃ : Subgroup G) : Subgroup G := H ⊓ centralizer (UH H V₃ : Set G)

/-- `U_L = ⟨U_H^L⟩`. -/
def UL (L H V₃ : Subgroup G) : Subgroup G := conjugateSpanBy (UH H V₃) L

/-- `D_H = C_{U_H}(Uγ/A₁)`, with local normalization supplied when used. -/
def DH (U_H Uγ A₁ : Subgroup G) : Subgroup G := commutatorPreimage U_H Uγ A₁

/-- `E_H = C_{V_H}(Uγ/A₁)`. -/
def EH (V_H Uγ A₁ : Subgroup G) : Subgroup G := commutatorPreimage V_H Uγ A₁

/-- `Dγ = C_{Uγ}(UH/V₁)`. The denominator is V₁, not A₁. -/
def Dgamma (Uγ U_H V₁ : Subgroup G) : Subgroup G := commutatorPreimage Uγ U_H V₁

/-- `Eγ = C_{Vγ}(UH/V₁)`. -/
def Egamma (Vγ U_H V₁ : Subgroup G) : Subgroup G := commutatorPreimage Vγ U_H V₁

end CFSG.Quasithin.Chapter13.Section08.Source

end

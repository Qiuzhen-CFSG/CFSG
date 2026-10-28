module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Chapter3.Defs
public import CFSG.Quasithin.ChapterE.Defs
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.ConjugacyFamilySpan
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The source hypotheses and constructions for §6.1

These definitions transcribe Hypothesis 6.1.1 and Theorem 6.1.27 of
Aschbacher–Smith, combined 1 March 2004 manuscript, printed pp.663 and 679
(PDF pp.680 and 696). The local family is Definition 1.2.3 with the
maximality and faithful condition on p.507; reduced modules are Definition
B.2.11. All normality and quotients are relative to their displayed groups.

A module identification consists of a quotient-group isomorphism and an
equivariant additive-group isomorphism, expressed multiplicatively. The
two different four-dimensional binary modules for A₅ and SL₂(4) are kept
distinct. No identification, reduction bound or centralizer conclusion is
assumed in `Hypothesis611`.

The weak closures are generated from the actual conjugates and their
subgroups of index `2^i`, as in E.3.13. We use the general E.1 family-span
definition: the current E.3 module and E.Defs both declare `ChapterE.weakClosure`
with different types and cannot yet be imported together.

The known-simple-class parameter has the meaning documented in
`Quasithin.Defs`. The final source theorem still needs to be proved;
`Conclusion6127` only specifies its target.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter6.Source

open Subgroup
open Theory.GroupTheory

universe u
variable {G : Type u} [Group G]

/-- `Ω₁(Z(H))`, embedded in the ambient group. -/
def centralOmega (H : Subgroup G) : Subgroup G :=
  omegaOneAmbient (H ⊓ centralizer (H : Set G))

/-- Definition 1.2.3. The Sylow condition is inside `⟨L,T⟩`. -/
def localFamily (T : Subgroup G) : Set (Subgroup G) :=
  {L | (L.subgroupOf (L ⊔ T)).IsCComponent ∧
    (∃ S : Sylow 2 ↥(L ⊔ T), (S : Subgroup ↥(L ⊔ T)).map (L ⊔ T).subtype = T) ∧
    (L ⊔ T).pCoreIn 2 ≠ ⊥}

/-- The class `X_f` of A.4.5–6 and p.507, including its internal module. -/
def faithfulLocal (L : Subgroup G) : Prop :=
  L ≠ ⊥ ∧ IsPPerfect 2 L ∧ generalizedFitting L = pCore 2 L ∧
    ⁅centralOmega (L.pCoreIn 2), L⁆ ≠ ⊥

/-- `L_f^*(G,T)`: maximality in `L(G,T)`, intersected with `X_f`. -/
def faithfulMaximalFamily (T : Subgroup G) : Set (Subgroup G) :=
  {L | Maximal (fun J => J ∈ localFamily T) L ∧ faithfulLocal L}

/-- Definition B.2.11: a normal elementary abelian subgroup whose
conjugation quotient has trivial two-core. This is not a rank condition. -/
def reducedFamily (H : Subgroup G) : Set (Subgroup G) :=
  {V | V ≤ H ∧ IsElementaryAbelian 2 V ∧
    ∃ hN : (V.subgroupOf H).Normal,
      letI := hN
      pCore 2 (H ⧸ centralizer (V.subgroupOf H : Set H)) = ⊥}

/-- The generated subgroup `R₂(H)` of B.2.12, distinguished from its family. -/
def reducedSubgroup (H : Subgroup G) : Subgroup G := sSup (reducedFamily H)

/-- An actual model for the action of `L/O₂(L)` on the ambient subgroup `V`.
The equality in `G` is the equivariance condition for conjugation by `l`. -/
def IsConjugationModel (L V : Subgroup G)
    {A X k : Type*} [Group A] [AddCommGroup X] [Semiring k] [Module k X]
    (ρ : Representation k A X) : Prop :=
  ∃ e : (L ⧸ pCore 2 L) ≃* A,
    ∃ f : V ≃* Multiplicative X,
      ∀ (l : L) (v : V),
        ((f.symm (Multiplicative.ofAdd
          (ρ (e (QuotientGroup.mk' (pCore 2 L) l))
            (Multiplicative.toAdd (f v))))) : G) =
          (l : G) * (v : G) * (l : G)⁻¹

/-- The binary deleted-permutation module for the actual alternating group. -/
def a5Module : Representation (ZMod 2) (alternatingGroup (Fin 5))
    (BinaryPermutation.natural (Fin 5)) :=
  (BinaryPermutation.naturalRepresentation (Fin 5)).comp
    (alternatingGroup (Fin 5)).subtype

/-- Exactly one or two copies of the A₅-module, with the same acting quotient
on both summands in the second case. -/
noncomputable def IsOneOrTwoA5Modules (L V : Subgroup G) : Prop :=
  IsConjugationModel L V a5Module ∨
    IsConjugationModel L V (a5Module.prod a5Module)

/-- The natural two-dimensional module in characteristic two. The acting
quotient is identified with SL₂ over the displayed field (equal to PSL₂
in characteristic two), and the ambient action is explicitly intertwined. -/
def IsNaturalModule (L V : Subgroup G) (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    Nat.card F = 2 ^ n ∧
      IsConjugationModel L V (Representation.specialLinearNatural (k := F) 2)

/-- The actual `W_i(X,V)` of E.3.13; conjugation ranges over all of `G`. -/
def W (V X : Subgroup G) (i : ℕ) : Subgroup G :=
  ChapterE.weakClosure X {A | ∃ g : G,
    A ≤ V.map (MulAut.conj g).toMonoidHom ∧
    A.relIndex (V.map (MulAut.conj g).toMonoidHom) = 2 ^ i}

/-- The source's `C_i(X,V)`. -/
def C (V X : Subgroup G) (i : ℕ) : Subgroup G :=
  X ⊓ centralizer (W V X i : Set G)

/-- The layer on which every assertion of 6.1.27 is made. -/
abbrev layer (L V : Subgroup G) : Subgroup G := ⁅V, L⁆

/-- `Z_S = C_{V_L}(T∩L)`, without replacing the initial `V` by `V_L`. -/
def ZS (T L V : Subgroup G) : Subgroup G :=
  layer L V ⊓ centralizer (T ⊓ L : Set G)

/-- All source assumptions of Hypothesis 6.1.1. The restriction `n > 1`
is the standing Chapter 5 rank-one parameter convention. -/
structure Hypothesis611 [Finite G] (K : GroupClass.{u}) (T : Sylow 2 G)
    (L M V : Subgroup G) (n : ℕ) : Prop where
  simpleQTKE : IsSimpleQTKE K G
  local_mem : L ∈ faithfulMaximalFamily (T : Subgroup G)
  quotient_model : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)
  n_gt_one : 1 < n
  maximal : IsMaximalTwoLocal M
  sylow_le : (T : Subgroup G) ≤ M
  L_le : L ≤ M
  L_normal : (L.subgroupOf M).Normal
  V_mem : V ∈ reducedFamily (L ⊔ (T : Subgroup G))
  nontrivial_action : layer L V ≠ ⊥
  not_a5 : ¬ IsOneOrTwoA5Modules L (layer L V)
  generation_one : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
    ChapterE.generationParameter H = 1

/-- All four conclusions of source Theorem 6.1.27, including the normalizer
of the genuine zeroth weak closure. This is a target, not an assumed result. -/
def Conclusion6127 (T L M V : Subgroup G) (n : ℕ) : Prop :=
  n = 2 ∧ IsNaturalModule L (layer L V) 2 ∧
    T ⊓ centralizer (L : Set G) = ⊥ ∧
    centralizer (ZS T L V : Set G) ≤ M ∧
    (¬ normalizer (W (layer L V) T 0 : Set G) ≤ M ∨
      ¬ W (layer L V) T 1 ≤ T ⊓ centralizer (ZS T L V : Set G))

end CFSG.Quasithin.Chapter6.Source

module

public import CFSG.Quasithin.Chapter6.Section01.SourceBasic

/-!
# The constructed subgroups in the escaping-centralizer branch

These are the groups introduced after Hypothesis 6.1.16 and in Lemma 6.1.21,
Aschbacher–Smith, combined 1 March 2004 manuscript, printed pp.672–676.
They are formed from the commutator layer of the *initial* `V`, so consumers
can use them before rewriting the initial module to that layer. The hypothesis
that the centralizer escapes `M` belongs to the lemmas, not these definitions.

`I` is the centralizer of the central line, and `H` is its normalizer; the
latter is the convention used from 6.1.21 onwards, not an arbitrary member of
the earlier family `HS`. Conjugation in `L1` and `E` is right conjugation
`U^l = l⁻¹ U l`. `R` is the two-core, whereas `HS` uses the two-residual.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter6.Source.Escape

open Subgroup

variable {G : Type*} [Group G]

def I (T L V : Subgroup G) : Subgroup G := centralizer (ZS T L V : Set G)

def H (T L V : Subgroup G) : Subgroup G := normalizer (ZS T L V : Set G)

/-- The family `𝓗_S` of p.672. -/
def HS (T L M V : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ Chapter1.HOver G (T : Set G) ∧ ¬ X ≤ M ∧
    (pResidual 2 X).map X.subtype ≤ I T L V}

/-- The orbit-generated subgroup `U = ⟨V_L^I⟩`. -/
def U (T L V : Subgroup G) : Subgroup G :=
  ChapterE.conjugateJoin (I T L V) (layer L V)

/-- `L₁ = ⟨U,U^l⟩`; the later lemmas require `l ∈ L − H`. -/
def L1 (T L V : Subgroup G) (l : G) : Subgroup G :=
  U T L V ⊔ (U T L V).map (MulAut.conj l⁻¹).toMonoidHom

def R (T L V : Subgroup G) (l : G) : Subgroup G := (L1 T L V l).pCoreIn 2

def E (T L V : Subgroup G) (l : G) : Subgroup G :=
  U T L V ⊓ (U T L V).map (MulAut.conj l⁻¹).toMonoidHom

/-- The orbit-generated subgroup contains the actual commutator layer. -/
theorem layer_le_U (T L V : Subgroup G) : layer L V ≤ U T L V := by
  intro x hx
  apply le_iSup (fun g : I T L V =>
    (layer L V).map (MulAut.conj (g : G)).toMonoidHom) 1
  exact mem_map.mpr ⟨x, hx, by simp⟩

end CFSG.Quasithin.Chapter6.Source.Escape

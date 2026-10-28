module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.Quasithin

/-!
# The subgroup collections in quasithin Chapter 1

These are Definitions 1.1.1 and 1.1.2 of Aschbacher–Smith,
*The Classification of Quasithin Groups* (combined manuscript, 1 March 2004,
pp. 499–500). Membership in `He` uses the source's equivalent centralizer
condition, so no generalized-Fitting-group convention is needed to use it.
All cores and centralizers in these definitions are viewed in the ambient group.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1

variable (G : Type*) [Group G]

/-- The collection `H`: subgroups with nontrivial two-core. -/
def H : Set (Subgroup G) := {K | K.pCoreIn 2 ≠ ⊥}

/-- The collection `He`: subgroups whose two-core contains its centralizer. -/
def He : Set (Subgroup G) :=
  {K | K ⊓ Subgroup.centralizer (K.pCoreIn 2 : Set G) ≤ K.pCoreIn 2}

/-- Members of `H` containing a specified subset. -/
def HOver (X : Set G) : Set (Subgroup G) := {K | K ∈ H G ∧ X ⊆ K}

/-- Members of `H(X)` not contained in `Y`. -/
def HOutside (X Y : Set G) : Set (Subgroup G) :=
  {K | K ∈ HOver G X ∧ ¬ (K : Set G) ⊆ Y}

/-- `He(X)` is the intersection of `He` with `H(X)`, not just its overgroups. -/
def HeOver (X : Set G) : Set (Subgroup G) := He G ∩ HOver G X

/-- `He(X,Y)` is the intersection of `He` with `H(X,Y)`. -/
def HeOutside (X Y : Set G) : Set (Subgroup G) := He G ∩ HOutside G X Y

/-- Nontrivial two-subgroups whose ambient normalizer belongs to `He`. -/
def S2e : Set (Subgroup G) :=
  {U | U ≠ ⊥ ∧ IsPGroup 2 U ∧ Subgroup.normalizer (U : Set G) ∈ He G}

variable {G}

/-- The actual inputs of Lemma 1.1.5. The involution lies in the center of
the chosen Sylow subgroup, equivalently in its central omega-one subgroup.
This structure contains only the hypotheses, not any classification conclusion. -/
structure Lemma115Hypotheses (K : Subgroup G) (S : Sylow 2 K)
    (M : Subgroup G) (z : G) : Prop where
  mem_H : K ∈ H G
  mem_HeOver : M ∈ HeOver G ((S : Subgroup K).map K.subtype : Set G)
  core_centralizer_le :
    M.pCoreIn 2 ⊓ Subgroup.centralizer ((K ⊓ M).pCoreIn 2 : Set G) ≤ K
  involution : orderOf z = 2
  mem_sylow : z ∈ (S : Subgroup K).map K.subtype
  central : ∀ s ∈ (S : Subgroup K).map K.subtype, s * z = z * s
  centralizer_le : Subgroup.centralizer ({z} : Set G) ≤ M

end CFSG.Quasithin.Chapter1

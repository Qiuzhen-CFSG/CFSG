module

public import CFSG.Quasithin.ChapterA.Section04.Basic
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# The subgroup families and intrinsic module of A.4

Definitions A.4.5–7 of Aschbacher–Smith, *The Classification of Quasithin
Groups*, printed pp. 58–59. Membership in X requires a nontrivial
2-perfect group whose generalized Fitting subgroup is its two-core.
The module V(X) is the already defined V(X,R) with R the embedded two-core.
The subfamily X_f consists of members for which this module is nontrivial.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterA.Section04

variable {G : Type*} [Group G]

/-- The collection X of Definition A.4.5, expressed as a membership predicate. -/
def IsSignalizerType (X : Subgroup G) : Prop :=
  X ≠ ⊥ ∧ IsPPerfect 2 X ∧
    Theory.GroupTheory.generalizedFitting X = pCore 2 X

/-- V(X) of Definition A.4.7. The intrinsic core is embedded in G. -/
def intrinsicSignalizerModule (X : Subgroup G) : Subgroup G :=
  signalizerModule X ((pCore 2 X).map X.subtype)

/-- Membership in X_f: source membership in X and a nontrivial module V(X). -/
def IsFaithfulSignalizerType (X : Subgroup G) : Prop :=
  IsSignalizerType X ∧ intrinsicSignalizerModule X ≠ ⊥

end CFSG.Quasithin.ChapterA.Section04

end

module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The source hypotheses for G.7

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.347--349. The ambient group is finite
and its binary module is faithful. In G.7.2 and G.7.3, its actual generalized
Fitting subgroup is quasisimple, SQTK, and irreducible on that module.
G.7.3 additionally bounds the degree by twice one more than the ambient
two-rank. No classification alternative is part of these hypotheses.

The class `K` remains explicit for independent deductions. The source
classification must instantiate it with the full known-simple catalogue.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section07

open Theory.GroupTheory

universe u v

variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- The exact standing assumptions of G.7.2 and G.7.3. SQTK is required of
`F*(G)`, as in the source, and irreducibility concerns its restricted action. -/
structure QuasisimpleSetup (K : GroupClass.{u})
    (ρ : Representation (ZMod 2) G V) [Finite G]
    [FiniteDimensional (ZMod 2) V] : Prop where
  faithful : Function.Injective ρ
  quasisimple : IsQuasisimple (generalizedFitting G)
  sqtk : IsSQTK K (generalizedFitting G)
  irreducible : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype)

/-- The additional inequality (*) in G.7.3. -/
def SmallDegree : Prop :=
  Module.finrank (ZMod 2) V ≤ 2 * (primeRank 2 G + 1)

end CFSG.Quasithin.ChapterG.Section07

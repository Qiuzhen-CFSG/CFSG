module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Control
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Definitions
public import CFSG.Quasithin.ChapterB.Section02.Thompson

/-!
# The original local groups in the proof of 15.3.67

These definitions fix the centralizers, Baumann subgroup, and core intersection
before the temporary replacement of `G_E`. In particular `lineS` is the two-core
of `Y_E T_E`; its equality with `C_T(E)` is a theorem to be proved, not a
definitional convention. The source's `C(G,B_E)` is
`Subgroup.characteristicNormalizerClosure (lineB T E)`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.67, printed p.1153, PDF p.1170.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
open Subgroup
variable {G : Type*} [Group G]

/-- `R = C_T(V)`. -/
def lineR (T V : Subgroup G) : Subgroup G := T ⊓ centralizer (V : Set G)

/-- `B_E = Baum(T_E)`, for the maximum elementary abelian Thompson subgroup. -/
noncomputable def lineB (T E : Subgroup G) : Subgroup G := ChapterB.baumann (lineT T E)

/-- `C_E = C_G(E)`. -/
abbrev lineC (E : Subgroup G) : Subgroup G := centralizer (E : Set G)

/-- `P_c = O₂(M_c) ∩ G_E`. -/
noncomputable def linePc (Mc E : Subgroup G) : Subgroup G :=
  Stellmacher.twoCoreAmbient Mc ⊓ lineNormalizer E

/-- `S_E = O₂(Y_E T_E)`, retaining the original line normalizer. -/
noncomputable def lineS (Y T E : Subgroup G) : Subgroup G :=
  Stellmacher.twoCoreAmbient (lineY Y E ⊔ lineT T E)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure

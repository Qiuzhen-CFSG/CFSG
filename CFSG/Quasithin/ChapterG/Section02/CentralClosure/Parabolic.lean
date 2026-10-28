module

public import CFSG.Quasithin.ChapterG.Section02.CentralClosure
public import CFSG.Quasithin.Chapter12.Section08.Defs

/-!
# G.2.2 on the marked U_H/V₁ of Section 12.8

Here the seed, point, Sylow subgroup, normal closure and quotient are the
literal constructions of Section 12.8. Applying G.2.2 gives its central
omega containment, embedded Frattini bound, relative normality and genuine
two-reducedness for each local subgroup J. The Section 12.8 source owner
supplies Hypothesis G.2.1 for that J; no conclusion of G.2.2 is a premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.2, printed p.332, applied in 12.8.4(2–3), printed p.850.
-/

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterG.Section02.CentralClosure
open CFSG.Quasithin.Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The actual U_J and its image in the flag's N_G(V₁)/V₁ satisfy G.2.2.
The centralizer in the reducedness assertion is inside the actual image of J. -/
public theorem parabolic_UH (F : InvariantFlag T V n) (L J : Subgroup G)
    (h : Setup.Hypothesis
      { V := V, V₁ := F.Vi 1, L := L, T := (T : Subgroup G), H := J }) :
    (F.tilde V ≤ F.tilde (F.UH J) ∧
      F.tilde (F.UH J) ≤ omegaOneAmbient
        ((center (F.tilde (J.pCoreIn 2))).map (F.tilde (J.pCoreIn 2)).subtype)) ∧
    (frattini (F.UH J)).map (F.UH J).subtype ≤ F.Vi 1 ∧
    (F.UH J ≤ (T : Subgroup G) ∧ ((F.UH J).subgroupOf (T : Subgroup G)).Normal) ∧
    IsPReduced 2 ((F.tilde (F.UH J)).subgroupOf (F.tilde J)) :=
  Setup.lemma_G_2_2 h

end CFSG.Quasithin.ChapterG.Section02.CentralClosure

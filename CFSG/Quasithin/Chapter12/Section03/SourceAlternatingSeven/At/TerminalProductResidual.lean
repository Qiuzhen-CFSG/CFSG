module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductResidual
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductSeed

/-!
# TerminalProductResidual at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductResidual`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

private theorem seven_outer_two_at : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 7))) := by
  let A := alternatingGroup (Fin 7)
  have hcard : Nat.card (Equiv.Perm (Fin 7) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by decide) (by decide)).surjective a
  exact ⟨QuotientGroup.mk' A σ, rfl⟩

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable (S : Setup T L V)

namespace TerminalPoint

variable {S} {D : S.LocalAnalysis} (P : TerminalPoint S D)

theorem L1_eq_ambient_residual_of_abelian_threeSylow_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (R : Sylow 3 (L ⧸ pCore 2 L)) (hR : IsMulCommutative R) :
    P.L1 = (primeToResidual 3 (centralizer (P.Z : Set G))).map
      (centralizer (P.Z : Set G)).subtype :=
  P.L1_eq_ambient_residual_at structural (S.normalizer_residual_of_abelian_threeSylow R hR)

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven


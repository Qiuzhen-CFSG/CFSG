module

public import Theory.GroupAction.PrimeSubgroupIncidence
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.NoSameColor
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Colors.Source

/-!
# The original six-parabolic incidence graph

The vertices are the six actual conjugate parabolics, with their original
involution colors and four-group containment. Edges are witnessed by
commuting order-five subgroups normalized by that same four-group.
The literal pair normalizer preserves incidence. Distinct members of
the original H-family cannot be adjacent, by their quotient pentagons.
Source: the graph E in J.4.10, printed p.444.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G}

/-- The graph uses the literal original subgroup vertices and witnesses. -/
def sourceGraph (p:Plane d) (B5:Sylow 5 d.toTypeRuSetup.H) (z u:G) :
    SimpleGraph (globalFamily p B5 z u) :=
  (Subgroup.PrimeIncidence.graph 5 (pairSpan z u)).induce (globalFamily p B5 z u)

/-- Exact source adjacency, without chosen five-subgroup representatives. -/
theorem sourceGraph_adj_iff (p:Plane d) (B5:Sylow 5 d.toTypeRuSetup.H) (z u:G)
    (E F:globalFamily p B5 z u) :
    (sourceGraph p B5 z u).Adj E F ↔
      (E:Subgroup G)≠(F:Subgroup G) ∧ ∃A B:Subgroup G,
      A≤E ∧ B≤F ∧ Nat.card A=5 ∧ Nat.card B=5 ∧
      pairSpan z u≤normalizer (A:Set G) ∧ pairSpan z u≤normalizer (B:Set G) ∧
      A≤centralizer (B:Set G) :=
  Subgroup.PrimeIncidence.adj_iff 5 (pairSpan z u) E F

/-- The genuine ambient normalizer action preserves original incidence. -/
theorem sourceGraph_action (p:Plane d) (B5:Sylow 5 d.toTypeRuSetup.H)
    (c:Choices d) (e:first≃*p.F₁ B5) (hz:(e modelZ:G)=c.z)
    (n:normalizer (pairSpan c.z (sourceU e):Set G))
    (E F:globalFamily p B5 c.z (sourceU e)) :
    (sourceGraph p B5 c.z (sourceU e)).Adj
      ((normalizerAction p B5 c e hz).smul n E)
      ((normalizerAction p B5 c e hz).smul n F) ↔
    (sourceGraph p B5 c.z (sourceU e)).Adj E F :=
  Subgroup.PrimeIncidence.conj_adj_iff (p:=5) (V:=pairSpan c.z (sourceU e))
    (E:=(E:Subgroup G)) (F:=(F:Subgroup G)) (n:G) n.property

/-- No original H-family has an internal incidence edge. -/
theorem not_adj_conjugate_family (p:Plane d) (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (V E F:Subgroup G) (hE:E∈conjugateFamily p B5) (hF:F∈conjugateFamily p B5) :
    ¬(Subgroup.PrimeIncidence.graph 5 V).Adj E F := by
  rw [Subgroup.PrimeIncidence.adj_iff]
  rintro ⟨hne,A,B,hAE,hBF,hA,hB,_,_,hc⟩
  exact hne (conjugate_parabolics_eq_of_commuting_fives p s B5 hi E F hE hF
    A B hAE hBF hA hB hc)

/-- In particular the two original z-colored source vertices are nonadjacent. -/
theorem sourceGraph_not_adj_base_color (p:Plane d) (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (c:Choices d) (e:first≃*p.F₁ B5) (hz:(e modelZ:G)=c.z)
    (E F:globalFamily p B5 c.z (sourceU e))
    (hE:(E:Subgroup G)∈colorFamily p B5 c.z (sourceU e) c.z)
    (hF:(F:Subgroup G)∈colorFamily p B5 c.z (sourceU e) c.z) :
    ¬(sourceGraph p B5 c.z (sourceU e)).Adj E F := by
  rw [colorFamily_z p B5 c e hz] at hE hF
  exact not_adj_conjugate_family p s B5 hi _ _ _ hE.1 hF.1
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily

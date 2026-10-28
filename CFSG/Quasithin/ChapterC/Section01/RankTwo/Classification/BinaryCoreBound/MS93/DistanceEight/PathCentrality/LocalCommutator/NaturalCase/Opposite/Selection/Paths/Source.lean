module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Transport

/-!
# The two conjugate spans in the initial opposite selection

The good conjugates satisfy the selected relative centralizer bound; the bad
conjugates fail that bound. Both spans use the original ordered pair and its
actual local conjugators. Their joins with the third-vertex radius group are
literal products, by relative normalization at that vertex.

These definitions separate the local span calculation from the geometric
escape of the original orbit. Neither calculation is assumed to follow just
from the definitions. The geometric assembly uses a proved good-span cover
and escape of this particular local span at distance b-2.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891,
the conjugate-span display multiplied by V_(alpha+3).
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The centralizer test at a specified prospective third vertex. -/
def GoodConjugate (a c t u : Vertex R) (g : stabilizer R c) : Prop :=
  Q R u ⊓ centralizer
    ((edgeCommutator R a t).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom :
      Set (FreeAmalgam R)) ≤ Q R c

/-- Span of precisely the conjugates satisfying the selected bound. -/
noncomputable def goodConjugateSpan (a c t u : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⨆ g : stabilizer R c, ⨆ _ : GoodConjugate a c t u g, Z R (act R g a)

/-- The bad-conjugate span in the displayed noncontainment on p.891. -/
noncomputable def badConjugateSpan (a c t u : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⨆ g : stabilizer R c, ⨆ _ : ¬ GoodConjugate a c t u g, Z R (act R g a)

theorem goodConjugateSpan_le (a c t u : Vertex R) :
    goodConjugateSpan a c t u ≤ localZSpan R a c := by
  apply iSup_le
  intro g
  exact iSup_le fun _ => le_iSup (fun h : stabilizer R c => Z R (act R h a)) g

theorem badConjugateSpan_le (a c t u : Vertex R) :
    badConjugateSpan a c t u ≤ localZSpan R a c := by
  apply iSup_le
  intro g
  exact iSup_le fun _ => le_iSup (fun h : stabilizer R c => Z R (act R h a)) g

/-- The two tests partition the original orbit; neither span alone is
asserted to generate it. -/
theorem localZSpan_eq_bad_sup_good (a c t u : Vertex R) :
    localZSpan R a c = badConjugateSpan a c t u ⊔ goodConjugateSpan a c t u := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro g
    by_cases h : GoodConjugate a c t u g
    · apply le_trans (b := goodConjugateSpan a c t u) _ le_sup_right
      exact le_iSup_of_le g (le_iSup (fun _ : GoodConjugate a c t u g =>
        Z R (act R g a)) h)
    · apply le_trans (b := badConjugateSpan a c t u) _ le_sup_left
      exact le_iSup_of_le g (le_iSup (fun _ : ¬ GoodConjugate a c t u g =>
        Z R (act R g a)) h)
  · exact sup_le (badConjugateSpan_le a c t u) (goodConjugateSpan_le a c t u)

variable {geometry : Geometry R}

/-- Normalization, hence the product interpretation, holds at the actual
third vertex and does not assert normality in the free amalgam. -/
theorem span_join_radius_eq_mul {a c u : Vertex R}
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (hcu : Adjacent R c u)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ localZSpan R a c) :
    (↑(K ⊔ V R u) : Set (FreeAmalgam R)) =
      (K : Set (FreeAmalgam R)) * (V R u : Set (FreeAmalgam R)) := by
  apply coe_mul_of_left_le_normalizer_right
  apply (hK.trans (localZSpan_le_Q R hc hd.le hb)).trans
  exact (show Q R c ≤ stabilizer R u from fun _ hx => hx.2 u hcu).trans
    (DistanceEight.V_normalized R u)

theorem badConjugateSpan_join_radius_eq_mul {a c t u : Vertex R}
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (hcu : Adjacent R c u) :
    (↑(badConjugateSpan a c t u ⊔ V R u) : Set (FreeAmalgam R)) =
      (badConjugateSpan a c t u : Set (FreeAmalgam R)) *
        (V R u : Set (FreeAmalgam R)) :=
  span_join_radius_eq_mul hc hd hb hcu _ (badConjugateSpan_le a c t u)

/-- The geometric input is escape of the specified ordered-pair orbit,
not escape of the larger radius group V_c. -/
def SpanEscape (geometry : Geometry R) (a c : Vertex R) : Prop :=
  ∃ e : Vertex R, (cosetGraph R).dist c e + 2 = geometry.b R ∧
    ¬ localZSpan R a c ≤ Q R e

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection

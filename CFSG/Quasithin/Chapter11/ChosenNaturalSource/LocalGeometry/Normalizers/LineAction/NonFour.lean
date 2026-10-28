module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2

/-!
# The line-action theorem outside field order four

The original component quotient is now recognized as J₁ whenever the
Sylow normalizer escapes N_G(L). Its field-degree constraint discharges
that normalizer premise for every nonbinary field of order greater than
four. The complete marked-family line-action theorem then gives both
original conclusions, retaining the literal line, residual and radical.

Only the already authorized radical alternative remains explicit here;
its final discharge belongs to qt-d-1222-natural-normalizer-source. The
field-four Sylow-normalizer terminal remains with this line-action task.
This specialization does not assert completion of the full theorem.

Source: Aschbacher--Smith, 3.3.16, printed p.591, and 11.2.3, pp.768--769.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Both source conclusions for all three marked families away from field order four. -/
theorem chosen_source_11_2_3_of_degree_ne_two
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hdegree : S.field.degree ≠ 2)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :=
  chosen_source_11_2_3_of_sylow_normalizer D S f hX
    (SylowNormalizer.sylow_normalizer_le_of_degree_ne_two f hdegree) hradical

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers

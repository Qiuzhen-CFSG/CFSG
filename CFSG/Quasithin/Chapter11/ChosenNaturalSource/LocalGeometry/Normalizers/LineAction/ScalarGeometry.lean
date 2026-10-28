module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.ScalarGeometry.Coordinates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.ScalarGeometry.Normalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.ScalarGeometry.Orbit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction

/-!
# Scalar geometry for the literal source line action

The supplied marking identifies V₁ with a field line when C_V(L)=1.
Its full scalar group is cyclic and regular on nonzero vectors. The full
SL₃, Sp₄ or G₂ action is nonzero-vector transitive; Sylow conjugacy in a
point stabilizer moves the transporter into N_L(T_L). Its inner Sylow
fixes the line, so the original odd Hall Cartan has exactly the same image.
Consequently the literal Cartan image is the entire transported scalar
group. T normalizes this image because it normalizes N_L(T_L).

`chosen_source_11_2_3_of_fixed_line_geometry` applies these facts to the
existing two-clause consumer, removing its hscalar premise. The sole
preceding identity needed for the scalar calculation is
`f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G)`, produced by
`qt-d-1222-natural-flag-cartan`. Final source assembly, including discharge
of that identity and the consumer's other earlier-source inputs, remains
with `qt-d-1222-natural-line-action`.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.0.2, the opening of §11.1, and 11.2.3, printed pp.759--761,768--769.
-/

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c)

/-- The actual Cartan image is the full scalar group for its original line marking. -/
theorem lineImage_eq_scalars {X : Subgroup G} (hX : IsCartan T L X)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hz : V ⊓ centralizer (L : Set G) = ⊥) :
    lineImage f X = (lineScalars f hz).range := by
  apply le_antisymm (lineImage_le_scalars f hz (hX.1.trans inf_le_left))
  rintro _ ⟨a,rfl⟩
  let : Nontrivial (f.Vi 0) := (Subgroup.nontrivial_iff_ne_bot _).mpr (f.V_ne_bot 0)
  obtain ⟨v,hv⟩ := exists_ne (0 : Additive (f.Vi 0))
  let e := lineCoordinates f hz
  let w := lineScalars f hz a v
  have hw : w ≠ 0 := fun h => hv ((lineScalars f hz a).injective
    (h.trans (map_zero _).symm))
  obtain ⟨n,hn⟩ := normalizer_line_transitive f hfixed (e v) (e w)
    (fun h => hv (e.injective (h.trans e.map_zero.symm)))
    (fun h => hw (e.injective (h.trans e.map_zero.symm)))
  let n' := inclusion (cartanNormalizer_normalizes_line f hfixed) n
  have hnact : lineAction f n' v = w := by
    apply e.injective
    apply Subtype.ext
    exact (lineProjection_component f ⟨n,n.property.1⟩ n'.property v).trans hn
  have hnmem : lineAction f n' ∈ lineImage f (cartanNormalizer T L) :=
    mem_map_of_mem _ n.property
  have hnscalar := lineImage_le_scalars f hz (H := cartanNormalizer T L) inf_le_left hnmem
  obtain ⟨z,_,hu⟩ := lineScalars_regular f hz v w hv hw
  have he : lineAction f n' = lineScalars f hz a := congrArg Subtype.val
    ((hu ⟨lineAction f n',hnscalar⟩ hnact).trans
      (hu ⟨lineScalars f hz a,MonoidHom.mem_range.mpr ⟨a,rfl⟩⟩ rfl).symm)
  rw [lineImage_cartan_eq_normalizer f hX hfixed, ← he]
  exact hnmem

/-- The three scalar facts required in source 11.2.3, with only its preceding
fixed-line identity retained. -/
theorem chosen_line_scalar_geometry {X : Subgroup G} (hX : IsCartan T L X)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hz : V ⊓ centralizer (L : Set G) = ⊥) :
    IsCyclic (lineImage f X) ∧ LinearGroup.IsRegularOnNonzero (lineImage f X) ∧
      lineImage f T ≤ normalizer (lineImage f X : Set _) := by
  refine ⟨?_,?_,lineImage_sylow_normalizes_cartan f hX hfixed⟩
  · rw [lineImage_eq_scalars f hX hfixed hz]
    exact lineScalars_isCyclic f hz
  · rw [lineImage_eq_scalars f hX hfixed hz]
    exact lineScalars_regular f hz

/-- Application to the literal two-clause consumer: its hscalar argument is
fully discharged. The fixed-line and other preceding geometry belongs to
qt-d-1222-natural-flag-cartan; the Sylow-normalizer and radical alternative
remain with qt-d-1222-natural-line-action's source assembly. -/
theorem chosen_source_11_2_3_of_fixed_line_geometry
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hfixR : f.Ri 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :=
  chosen_source_11_2_3_of_line_geometry D S f hX hfixed hm hfix hfixR hNT
    (chosen_line_scalar_geometry f hX hfixed) hradical
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers

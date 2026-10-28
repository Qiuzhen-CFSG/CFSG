module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.PointPlacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Membership
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan

/-!
# Recognition of the reselected first residual

A local component contained in a natural flag residual must equal it. The
marked flag supplies the literal PSL₂ quotient; the rank-one covering
theorem rules out a proper local component. Applying this to the omega-center
placement identifies the reselected first residual with the actual K₀.

The quotient model is derived from the natural input, rather than imposed
as an additional recognition hypothesis. The original-triangle application
is in Forward/Source.lean.
Source: Aschbacher–Smith, 11.1.2(3), printed p.764.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
open LocalGeometry LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I U : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T I U) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

private theorem local_eq_flag_residual_of_equiv (i : Fin 2) (A : Subgroup G)
    (hA : A ∈ Chapter1.L G T) (hAB : A ≤ f.Li i)
    (e : (f.Li i ⧸ pCore 2 (f.Li i)) ≃* PSL(2, S.field.Carrier)) : A = f.Li i := by
  let B := f.Li i
  have hB := flag_mem_local_of_model D S f i
    ⟨S.field.Carrier, inferInstance, inferInstance, S.field.card_eq, ⟨e⟩⟩
  let H := B ⊔ (T : Subgroup G)
  have hAH : A ≤ H := hAB.trans le_sup_left
  let P := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let A' := A.subgroupOf H
  let B' := B.subgroupOf H
  let b : B' ≃* B := subgroupOfEquivOfLe (show B ≤ H from le_sup_left)
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let e' := bq.trans e
  let : Group.IsPerfect B' := hB.1.perfect
  have hfour : 4 ≤ Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (show (4 : ℕ) = 2 ^ 2 from rfl).le.trans
      (Nat.pow_le_pow_right (by decide) S.nonbinary)
  let : IsSimpleGroup PSL(2, S.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup (B' ⧸ pCore 2 B') := e'.isSimpleGroup
  have hz : center (B' ⧸ pCore 2 B') = ⊥ := by
    rcases (inferInstance : (center (B' ⧸ pCore 2 B')).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative (B' ⧸ pCore 2 B')
        (center_eq_top_iff.mp ht)).elim
  let : IsQuasisimple (B' ⧸ pCore 2 B') :=
    { toIsPerfect := inferInstance
      simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  have hA' : A' ∈ ChapterA.Section03.localCComponents P := by
    exact ((Chapter1.mem_LIn_iff_subgroupOf
      (show (T : Subgroup G) ≤ H from le_sup_right) hAH).mp ⟨hAH,hA⟩).1
  let eSL := e'.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := S.field.Carrier)).symm
  let q := eSL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B'))
  have hsur : Function.Surjective q := eSL.surjective.comp (QuotientGroup.mk'_surjective _)
  have he : A' = B' := ChapterA.Section03.SourceEmbeddings.eq_of_rankOne_cover P
    hA' hB.1 (comap_mono hAB) q hsur
  simpa only [A', B', map_subgroupOf_eq_of_le hAH,
    map_subgroupOf_eq_of_le (show B ≤ H from le_sup_left)] using congrArg (map H.subtype) he

/-- A nonbinary natural flag residual cannot properly contain another
local component. Its rank-one quotient is supplied by the marked flag. -/
theorem local_eq_flag_residual (i : Fin 2) (A : Subgroup G)
    (hA : A ∈ Chapter1.L G T) (hAB : A ≤ f.Li i) : A = f.Li i := by
  obtain ⟨f₀,hunique,_,hquot,_⟩ := exists_unique_marked_flag D S c
  have he : f.Li i = f₀.Li i := by
    change localResidual I (c.preimage (f.space i.castSucc)) = _
    rw [hunique i.castSucc (f.space i.castSucc) (f.dimension i.castSucc)
      (f.invariant i.castSucc)]
    rfl
  have hquot' : Nonempty ((f.Li i ⧸ pCore 2 (f.Li i)) ≃* PSL(2, S.field.Carrier)) := by
    rw [he]
    exact hquot i
  exact local_eq_flag_residual_of_equiv D S f i A hA hAB hquot'.some

/-- The actual K₀ in the field-four triangle is the new first residual. -/
theorem triangle_other_eq_firstResidual
    {L₂ K K₀ : Subgroup G}
    (hI : I = K₀ ⊔ L₂) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ ≤ K)
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (hfix : U ⊓ centralizer (I : Set G) = ⊥) :
    f.Li 0 = K₀ := by
  exact (local_eq_flag_residual D S f 0 K₀ hK₀
    (triangle_other_le_firstResidual D S f hI hK₀ hK₀K hKZ hfix).2).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection

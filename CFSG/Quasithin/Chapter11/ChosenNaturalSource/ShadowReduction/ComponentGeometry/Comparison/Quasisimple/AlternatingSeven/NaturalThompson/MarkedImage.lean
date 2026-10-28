module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson.Containment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson.SeedCentralizer

/-!
# Original Thompson elements in the marked local action

Apply the original Thompson factorization inside KzT. The original flag
makes every Sylow element normalize L1. The quotient-centralizing factor
therefore fixes the literal seed image, by perfect central-cover rigidity.
The remaining factor is exactly the image of T intersect L. InnerSylow
and InnerImage complete its natural parabolic calculation.

This intermediate application supplies the quotient-centralizing factor
in the final marked innerness argument of Aschbacher--Smith 11.4.2, printed p.777. The completed ThompsonInnerImage
application is in InnerImage. The earlier actual PSL2 quotient marking is produced by
qt-d-1222-natural-flag-cartan; final A7 assembly is qt-d-1222-quasisimple-a7.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The part of the original inner Sylow seen in the literal local action. -/
def innerSylowImage : Subgroup (ActionQuotient E) :=
  (((T : Subgroup G) ⊓ L).subgroupOf (localGroup E)).map (projection E)

/-- Original Thompson control transported to the actual marked action quotient.
The component Sylow factor remains explicit for the parabolic calculation. -/
theorem projection_mem_innerSylow_join_centralizer
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel E)
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hT : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G))
    (a : localGroup E) (ha : (a : G) ∈ elementaryAbelianMaxJ (T : Subgroup G)) :
    projection E a ∈ innerSylowImage E ⊔
      centralizer (seedImage E : Set (ActionQuotient E)) := by
  obtain ⟨l,hl,c,hc,he⟩ := thompson_factorization E.input ha
  let l' : localGroup E := ⟨l,(le_sup_right : (T : Subgroup G) ≤ localGroup E) hl.1⟩
  let c' : localGroup E := ⟨c,(le_sup_right : (T : Subgroup G) ≤ localGroup E) hc.1⟩
  have he' : a = l' * c' := Subtype.ext he
  rw [he',map_mul]
  apply (innerSylowImage E ⊔ centralizer (seedImage E : Set (ActionQuotient E))).mul_mem
  · exact mem_sup_left ⟨l',hl,rfl⟩
  · exact mem_sup_right (projection_centralizes_seedImage_of_coreQuotientCentralizer
      E hstar hmodel e c' (hT hc.1) hc.2)

/-- The literal original invariant flag supplies seed normalization; the
only rank-one input is its earlier actual PSL2 quotient marking. -/
theorem ofFlag_projection_mem_innerSylow_join_centralizer
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel (ofFlag S f X z H))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (a : localGroup (ofFlag S f X z H))
    (ha : (a : G) ∈ elementaryAbelianMaxJ (T : Subgroup G)) :
    projection (ofFlag S f X z H) a ∈ innerSylowImage (ofFlag S f X z H) ⊔
      centralizer (seedImage (ofFlag S f X z H) : Set (ActionQuotient (ofFlag S f X z H))) :=
  projection_mem_innerSylow_join_centralizer _ hstar hmodel e
    (f.sylow_normalizes_Li 0) a ha

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson

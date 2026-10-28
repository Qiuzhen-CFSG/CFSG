module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Inputs

/-!
# Correcting root J₂ marks by the placed cubic

Separate simultaneous placement of the cubic and dihedral subgroups from the
coordinate action of the inverter. The two subgroup inclusions are equalities
for an injective map, by their checked orders three and ten. Multiplying the
ambient conjugator on the left by a long-cubic element preserves both marks:
the cubic is abelian and centralizes the placed dihedral group.

If the inverter acts as a long-cubic element followed by the graph action,
conjugation by that same cubic element gives the exact graph action. Indeed,
the graph inverts the cubic and the cube of the correcting element is one.
This argument uses the literal additive coordinates and quotient action;
it requires no equality with `L.swap` or faithfulness of the whole centralizer.

The consumer in `RootJ2Alignment` assembles this correction with two explicit
source premises. Simultaneous subgroup placement and the inverter coset
assertion are not proved here. Source: Aschbacher, *Sporadic Groups* (1994),
proof of Lemma 49.5, pp.283–284, using 49.1 (p.280) and 48.8 (p.273).
-/

open Matrix Atlas.Conway
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals

structure RootJ2SubgroupMarks (L : LongFrame)
    (f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient) : Prop where
  cubic_le : (longCubic L).range ≤ Sporadic.LeechRelated.J2.RecognitionGeometry.X.map f
  dihedral_le : (dihedralLift L).range ≤ Sporadic.LeechRelated.J2.RecognitionGeometry.B.map f

theorem conjugatedRootJ2_injective
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (g : LeechCentralQuotient) : Function.Injective (conjugatedRootJ2 e g) :=
  (MulAut.conj g).injective.comp (icosianProjectiveToCo1_injective.comp e.injective)

variable {L : LongFrame} {f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient}

theorem RootJ2SubgroupMarks.cubic_eq (M : RootJ2SubgroupMarks L f)
    (hf : Function.Injective f) :
    (longCubic L).range = Sporadic.LeechRelated.J2.RecognitionGeometry.X.map f := by
  apply Subgroup.eq_of_le_of_card_ge M.cubic_le
  rw [Subgroup.card_map_of_injective hf, longCubic_card,
    Sporadic.LeechRelated.J2.RecognitionGeometry.card_X]

theorem RootJ2SubgroupMarks.dihedral_eq (M : RootJ2SubgroupMarks L f)
    (hf : Function.Injective f) :
    (dihedralLift L).range = Sporadic.LeechRelated.J2.RecognitionGeometry.B.map f := by
  apply Subgroup.eq_of_le_of_card_ge M.dihedral_le
  rw [Subgroup.card_map_of_injective hf, dihedralLift_card,
    Sporadic.LeechRelated.J2.RecognitionGeometry.card_B]

theorem conjugatedRootJ2_mul
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (c g : LeechCentralQuotient) (a : Sporadic.LeechRelated.J2.Carrier) :
    conjugatedRootJ2 e (c * g) a = c * conjugatedRootJ2 e g a * c⁻¹ := by
  simp [conjugatedRootJ2, MulAut.conj_apply, mul_assoc]

theorem RootJ2SubgroupMarks.conjugate_cubic
    {e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel}
    {g : LeechCentralQuotient}
    (M : RootJ2SubgroupMarks L (conjugatedRootJ2 e g)) (t : Fˣ) :
    RootJ2SubgroupMarks L (conjugatedRootJ2 e (longCubic L t * g)) := by
  constructor
  · rintro a ⟨s, rfl⟩
    obtain ⟨x, hx, he⟩ := M.cubic_le ⟨s, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [conjugatedRootJ2_mul, he]
    have hc : Commute (longCubic L t) (longCubic L s) :=
      (Commute.all t s).map (longCubic L)
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  · rintro a ⟨d, rfl⟩
    obtain ⟨x, hx, he⟩ := M.dihedral_le ⟨d, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [conjugatedRootJ2_mul, he, (longCubic_commutes_dihedral L t d).eq,
      mul_assoc, mul_inv_cancel, mul_one]

private theorem torus_inv (t : Fˣ) : (torus t)⁻¹ = torus t⁻¹ := by
  apply Subtype.ext
  change (!![(t : F),0;0,((t⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F).adjugate = _
  simp [torus, Matrix.adjugate_fin_two]

private theorem graph_torus (t : Fˣ) (v : Fin 6 → F) :
    action graph (pairRepresentation (torus t⁻¹, (torus t⁻¹)⁻¹) v) =
      pairRepresentation (torus t, (torus t)⁻¹) (action graph v) := by
  rw [← graph_action, ← graph_action, torus_inv, torus_inv]
  change pairAction (flip, flip) (pairAction (torus t⁻¹, torus (t⁻¹)⁻¹) v) =
    pairAction (torus t, torus t⁻¹) (pairAction (flip, flip) v)
  funext i
  fin_cases i <;> simp [pairAction, flip, torus]

theorem longCubic_cube (L : LongFrame) (t : Fˣ) : longCubic L t ^ 3 = 1 := by
  have hc : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, GaloisField.card 2 2 (by decide)]
    norm_num
  have ht : t ^ 3 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := t))
  rw [← map_pow, ht, map_one]

theorem graph_action_of_cubic_coset (L : LongFrame) (a : LeechCentralQuotient)
    (t : Fˣ)
    (ha : ∀ v : Fin 6 → F,
      quotientModTwoRepresentation a (L.coordinates v) =
        quotientModTwoRepresentation (longCubic L t) (L.coordinates (action graph v)))
    (v : Fin 6 → F) :
    quotientModTwoRepresentation (longCubic L t * a * (longCubic L t)⁻¹)
        (L.coordinates v) = L.coordinates (action graph v) := by
  rw [map_mul, map_mul]
  change quotientModTwoRepresentation (longCubic L t)
    (quotientModTwoRepresentation a
      (quotientModTwoRepresentation ((longCubic L t)⁻¹) (L.coordinates v))) = _
  rw [← map_inv, longCubic_action, ha, graph_torus, ← longCubic_action]
  have he : ∀ w,
      quotientModTwoRepresentation (longCubic L t)
        (quotientModTwoRepresentation (longCubic L t)
          (quotientModTwoRepresentation (longCubic L t) w)) = w := by
    intro w
    have h := congrArg (fun k => quotientModTwoRepresentation k w) (longCubic_cube L t)
    simpa only [pow_succ, pow_zero, one_mul, map_mul, map_one,
      LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] using h
  exact he _


/-- Correct the reflection without changing the placed cubic and dihedral groups. -/
theorem rootJ2MarksOfCubicCoset (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (g : LeechCentralQuotient)
    (M : RootJ2SubgroupMarks L (conjugatedRootJ2 e g)) (t : Fˣ)
    (ha : ∀ v : Fin 6 → F,
      quotientModTwoRepresentation
          (conjugatedRootJ2 e g Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.inverter)
          (L.coordinates v) =
        quotientModTwoRepresentation (longCubic L t) (L.coordinates (action graph v))) :
    RootJ2Marks L (conjugatedRootJ2 e (longCubic L t * g)) := {
  cubic_le := (M.conjugate_cubic t).cubic_le
  dihedral_le := (M.conjugate_cubic t).dihedral_le
  reflection_on_single := by
    intro j a
    rw [conjugatedRootJ2_mul]
    exact graph_action_of_cubic_coset L _ t ha (Pi.single j a) }


end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

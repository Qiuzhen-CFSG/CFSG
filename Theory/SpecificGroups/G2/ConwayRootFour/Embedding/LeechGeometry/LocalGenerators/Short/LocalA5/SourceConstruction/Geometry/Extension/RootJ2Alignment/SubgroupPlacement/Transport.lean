module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.Reduction

/-!
# Transport of the marked dihedral group into a long frame

The natural three coordinates prove faithfulness of every `LongFrame.long`.
When a conjugated root J₂ cubic contains the long cubic, its marked D₁₀
centralizes that cubic. A separate ambient centralizer bound therefore places
D₁₀ in the long subgroup, where the faithful long map gives its exact matrix
pullback. Conjugation inside the long subgroup preserves the cubic mark.

`SubgroupPlacement` uses these results to combine the ambient cubic geometry
with conjugacy of D₁₀ subgroups of SL₃(4). No ambient orbit or centralizer
classification is asserted here. The matrix model retains the precise block,
field comparison and dihedral conventions of `SourceConstruction.Placement`.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 49.5, pp.283–284;
the root J₂ is chosen using 49.1 (p.280), and the local placement uses
48.3, 49.2 and 48.8 (p.273).
-/

open Matrix Atlas.Conway
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight

/-- The dihedral matrices before applying the chosen long embedding. -/
def rootJ2LongDihedralModel : DihedralGroup 5 →* SL(3,F) :=
  block.comp (slEquiv.toMonoidHom.comp dihedralModel)

theorem rootJ2LongDihedralModel_apply (L : LongFrame) (d : DihedralGroup 5) :
    L.long (rootJ2LongDihedralModel d) = dihedralLift L d := rfl

theorem longFrame_long_injective (L : LongFrame) : Function.Injective L.long := by
  intro A B h
  have he (v : Fin 6 → F) :
      action (BlockRealization.blockHom A) v = action (BlockRealization.blockHom B) v := by
    apply L.coordinates_injective
    rw [← L.intertwines_long, ← L.intertwines_long, h]
  have hn (v : Fin 3 → F) : A.val *ᵥ v = B.val *ᵥ v := by
    have hv := he ![v 0,0,0,v 1,v 2,0]
    rw [action_block, action_block] at hv
    have hvec : ![v 0,v 1,v 2] = v := by
      ext i
      fin_cases i <;> rfl
    funext i
    fin_cases i
    · simpa [hvec] using congrFun hv 0
    · simpa [hvec] using congrFun hv 3
    · simpa [hvec] using congrFun hv 4
  apply Subtype.ext
  ext i j
  simpa using congrFun (hn (Pi.single j 1)) i

theorem longFrame_range_le_cubicCentralizer (L : LongFrame) :
    L.long.range ≤ centralizerI ⊓
      Subgroup.centralizer ((longCubic L).range : Set LeechCentralQuotient) := by
  rintro a ⟨A, rfl⟩
  refine ⟨L.long_mem A, ?_⟩
  rintro c ⟨t, rfl⟩
  exact (longCubic_commutes_long L t A).eq

theorem rootJ2_dihedral_le_cubicCentralizer
    (L : LongFrame) (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    {g : LeechCentralQuotient} (hg : g ∈ centralizerI)
    (hX : (longCubic L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g)) :
    Sporadic.LeechRelated.J2.RecognitionGeometry.B.map (conjugatedRootJ2 e g) ≤
      centralizerI ⊓ Subgroup.centralizer ((longCubic L).range : Set LeechCentralQuotient) := by
  rintro a ⟨b, hb, rfl⟩
  refine ⟨conjugatedRootJ2_mem e hg b, ?_⟩
  intro c hc
  obtain ⟨x, hx, rfl⟩ := hX hc
  have hxK := Sporadic.LeechRelated.J2.RecognitionGeometry.X_sup_Y_le_K
    (show x ∈ Sporadic.LeechRelated.J2.RecognitionGeometry.X ⊔
      Sporadic.LeechRelated.J2.RecognitionGeometry.Y from Subgroup.mem_sup_left hx)
  have hcomm : b * x = x * b := hxK b hb
  simpa only [map_mul] using congrArg (conjugatedRootJ2 e g) hcomm.symm

/-- Pull the literal marked dihedral group back through the faithful long map. -/
def rootJ2DihedralPullback (L : LongFrame)
    (f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient)
    (hB : Sporadic.LeechRelated.J2.RecognitionGeometry.B.map f ≤ L.long.range) :
    DihedralGroup 5 →* SL(3,F) :=
  (MonoidHom.ofInjective (longFrame_long_injective L)).symm.toMonoidHom.comp
    ((f.comp Sporadic.LeechRelated.J2.RecognitionGeometry.dihedralHom).codRestrict
      L.long.range (fun d => hB ⟨_, by
        rw [← Sporadic.LeechRelated.J2.RecognitionGeometry.dihedralHom_range]
        exact ⟨d, rfl⟩, rfl⟩))

theorem rootJ2DihedralPullback_spec (L : LongFrame)
    (f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient)
    (hB : Sporadic.LeechRelated.J2.RecognitionGeometry.B.map f ≤ L.long.range)
    (d : DihedralGroup 5) :
    L.long (rootJ2DihedralPullback L f hB d) =
      f (Sporadic.LeechRelated.J2.RecognitionGeometry.dihedralHom d) :=
  MonoidHom.apply_ofInjective_symm (longFrame_long_injective L) _

theorem rootJ2DihedralPullback_injective (L : LongFrame)
    (f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient)
    (hf : Function.Injective f)
    (hB : Sporadic.LeechRelated.J2.RecognitionGeometry.B.map f ≤ L.long.range) :
    Function.Injective (rootJ2DihedralPullback L f hB) := by
  intro d d' h
  apply Sporadic.LeechRelated.J2.RecognitionGeometry.dihedralHom_injective
  apply hf
  simpa only [rootJ2DihedralPullback_spec] using congrArg L.long h

/-- A second conjugation inside the long group preserves the cubic mark. -/
theorem rootJ2_cubic_mark_long_conjugate (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (g : LeechCentralQuotient)
    (hX : (longCubic L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g))
    (A : SL(3,F)) :
    (longCubic L).range ≤ Sporadic.LeechRelated.J2.RecognitionGeometry.X.map
      (conjugatedRootJ2 e (L.long A * g)) := by
  rintro c ⟨t, rfl⟩
  obtain ⟨x, hx, he⟩ := hX ⟨t, rfl⟩
  refine ⟨x, hx, ?_⟩
  rw [conjugatedRootJ2_mul, he, ← (longCubic_commutes_long L t A).eq,
    mul_assoc, mul_inv_cancel, mul_one]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

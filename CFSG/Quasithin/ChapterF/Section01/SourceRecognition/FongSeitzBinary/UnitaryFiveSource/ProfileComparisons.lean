module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NativeData
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NativeComparisons

/-!
# U₅ recognition from the actual earlier mixed-factor profile

The original profile supplies the synchronized source construction's exact
field, rank-one covering and local-core inputs. The remaining coordinate,
Cartan, reflection and braid equations are proved by NativeData. Its actual
FiveData now constructs the marked model comparison on the same quotient,
including arbitrary field universes and both endpoint orientations.
The reduced application proves the existing FiveSourceTheorem interface;
earlier source quotient, split datum and row selection remain explicit.
Source: Fong--Seitz I (6A)(c), II (8C), pp.202--210; DGS Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
open UnitaryPresentation UnitarySource.Combined
variable {G X K E : Type*} [Group G] [Group X]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (hm : rotationOrder Q = 4)
  (n : ℕ) (hn : 0 < n) (i j : Fin 2) (hij : i ≠ j)
  (p : FiveProfile L S Q split K E n i j)

include mark h hm hn hij p in
/-- The entire equation package is constructed from the literal earlier
profile; no presentation law or generation premise is supplied. -/
theorem profile_native_data : Nonempty (FiveData Q split j (fiveForm p.form)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨g,θ,b,γ,ξ,d,_⟩ := marked_native_data Q split mark h p.form n p.linear_card p.unitary_card
    p.fixed_card p.matrix p.conjugation hm i j hij p.linear_remainder p.unitary_remainder
    p.linear_reflection p.unitary_reflection p.linear_actor p.linear_surjective p.linear_kernel
    p.unitary_panel p.cover p.cover_surjective p.cover_square p.linear_index p.unitary_index
    p.linear_sylow_elementary p.unitary_derived p.unitary_frattini
  exact ⟨d⟩

include mark h hm hn hij p in
/-- Both original endpoints and the whole Borel use one projective equivalence. -/
theorem profile_model_comparison :
    ∃ (M : GreenBook.UnitaryFive.Model (2^n)) (f : M.Carrier ≃* (X ⧸ Q.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag M.leftParabolic M.rightParabolic j)),
      M.overlap.map f.toMonoidHom = Q.tits.B ∧
      (∀ a : parabolic L S 0, (c.left a : M.Carrier) = f.symm (mark.left a : X ⧸ Q.D)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : M.Carrier) = f.symm (mark.middle a : X ⧸ Q.D)) ∧
      (∀ a : parabolic L S 1, (c.right a : M.Carrier) = f.symm (mark.right a : X ⧸ Q.D)) := by
  obtain ⟨d⟩ := profile_native_data Q split mark h hm n hn i j hij p
  obtain ⟨M,f,hL,hP⟩ := fiveData_model_marking p.form n p.unitary_card p.conjugation Q split hm
    (source_center_eq_bot Q mark h split) p.fixed_card d
  exact ⟨M,f,mark.trans (MarkedAmalgam.fromSource Q _ _ j f hL hP),
    MarkedAmalgam.map_overlap Q _ _ j f hL hP,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

include mark h hm hn hij p in
/-- Another marked presentation of the same quotient uses the same source
model and one equivalence on all three flag groups. -/
theorem profile_model_other_comparison {A B C : Type*} [Group A] [Group B] [Group C]
    (α : RankTwoAmalgam A B C) (other : RankTwoAmalgam.Iso α Q.standardAmalgam) :
    ∃ (M : GreenBook.UnitaryFive.Model (2^n)) (f : M.Carrier ≃* (X ⧸ Q.D))
      (c : RankTwoAmalgam.Iso α (MarkedAmalgam.flag M.leftParabolic M.rightParabolic j)),
      M.overlap.map f.toMonoidHom = Q.tits.B ∧
      (∀ a : A, (c.left a : M.Carrier) = f.symm (other.left a : X ⧸ Q.D)) ∧
      (∀ b : B, (c.middle b : M.Carrier) = f.symm (other.middle b : X ⧸ Q.D)) ∧
      (∀ a : C, (c.right a : M.Carrier) = f.symm (other.right a : X ⧸ Q.D)) := by
  obtain ⟨d⟩ := profile_native_data Q split mark h hm n hn i j hij p
  obtain ⟨M,f,hL,hP⟩ := fiveData_model_marking p.form n p.unitary_card p.conjugation Q split hm
    (source_center_eq_bot Q mark h split) p.fixed_card d
  exact ⟨M,f,other.trans (MarkedAmalgam.fromSource Q _ _ j f hL hP),
    MarkedAmalgam.map_overlap Q _ _ j f hL hP,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

/-- The original source interface is proved in all its field universes.
The existing restoration consumer receives this exact earlier profile. -/
theorem five_source_theorem {G X : Type*} [Group G] [Group X]
    {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso (DGS85.OriginalExtension.reducedAmalgam L S) Q.standardAmalgam)
    (split : SplitData Q.tits) : FiveSourceTheorem Q e split := by
  intro h hm K E _ _ _ _ _ _ n hn line p
  have hij : (if line then (1 : Fin 2) else 0) ≠ (if line then 0 else 1) := by
    cases line <;> decide
  obtain ⟨d⟩ := profile_native_data Q split ((intersectionToReduced h).trans e)
    (SuzukiContainment.reduced_hypothesis h) hm n hn _ _ hij p
  exact ⟨reducedFiveComparison p.form n p.unitary_card p.conjugation h Q e split hm p.fixed_card line d⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

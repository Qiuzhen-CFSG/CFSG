module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NativeAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.CombinedSource
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.RootCharts
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.FieldTransport

/-!
# The marked U₅ model on the synchronized source field

The three-dimensional source form determines the five-dimensional identity
form on the same field. Trace surjectivity supplies the model basis parameter.
The constructed FiveData then gives the actual projective model, its entire
scalar kernel, both parabolics and their full overlap. The reduced comparison
is exactly the input to the existing original-extension restoration.
Source: Fong--Seitz II (8C), pp.202--210; DGS Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Theory.SpecificGroups.UnitaryFive
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
open UnitaryPresentation

section SmallModel
variable {E : Type} [Field E] [Finite E] [CharP E 2]
  (J : HermitianForm 3 E) (n : ℕ)
  (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))

/-- The published general-q model uses the actual synchronized source field. -/
def sourceModel : GreenBook.UnitaryFive.Model (2^n) where
  F := E
  form := fiveForm J
  card := hE
  conjugation := hconj
  matrix := rfl

end SmallModel

variable {E : Type*} [Field E] [Finite E] [CharP E 2]
  (J : HermitianForm 3 E) (n : ℕ)
  (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))

private def SmallCarrier (k : ℕ) : Type := Fin k

include hE hconj in
/-- A finite source field in any universe supplies the published small model,
with the entire scalar quotient and the literal line-plane flag preserved. -/
theorem small_source_model :
    ∃ (M : GreenBook.UnitaryFive.Model (2^n))
      (f : ProjectiveSpecialUnitaryMatrixGroup (fiveForm J) ≃* M.Carrier)
      (a : (fiveForm J).specialSubgroup ≃* M.form.specialSubgroup),
      (∀ x, f (project (fiveForm J) x) = project M.form (a x)) ∧
      (lineParabolic (fiveForm J)).map f.toMonoidHom = M.leftParabolic ∧
      (planeParabolic (fiveForm J)).map f.toMonoidHom = M.rightParabolic := by
  let : Fintype E := Fintype.ofFinite E
  let F := SmallCarrier (Fintype.card E)
  let φ : F ≃ E := (Fintype.equivFin E).symm
  let : Finite F := Finite.of_equiv E φ.symm
  let : Field F := φ.field
  let e : E ≃+* F := (Equiv.ringEquiv φ).symm
  let : CharP F 2 := e.symm.toRingHom.charP e.symm.injective 2
  let σ : F ≃+* F := (e.symm.trans J.conj).trans e
  have hσ : Function.Involutive σ := by
    intro x
    simp only [σ,RingEquiv.trans_apply,e.symm_apply_apply]
    rw [J.conj_involutive (e.symm x),e.apply_symm_apply]
  let K := identityForm σ hσ
  have hc (x : E) : e ((fiveForm J).conj x) = K.conj (e x) := by
    change e (J.conj x) = e (J.conj (e.symm (e x)))
    rw [e.symm_apply_apply]
  have hform : (fiveForm J).form.map e = K.form := by
    change (1 : Matrix (Fin 5) (Fin 5) E).map e = 1
    exact Matrix.map_one e (map_zero e) (map_one e)
  let M : GreenBook.UnitaryFive.Model (2^n) :=
    { F := F
      form := K
      card := (Nat.card_congr e.symm.toEquiv).trans hE
      conjugation := fun x => by
        change e (J.conj (e.symm x)) = x ^ (2^n)
        rw [hconj,map_pow,e.apply_symm_apply]
      matrix := rfl }
  exact ⟨M,FieldTransport.projectiveEquiv e (fiveForm J) K hc hform,
    FieldTransport.specialEquiv e (fiveForm J) K hc hform,
    FieldTransport.projectiveEquiv_project e (fiveForm J) K hc hform,
    FieldTransport.map_line e (fiveForm J) K hc hform,
    FieldTransport.map_plane e (fiveForm J) K hc hform⟩

omit [CharP E 2] in
include hE in
/-- The original fixed-field count supplies the only auxiliary model-basis parameter. -/
theorem source_trace_one (hfixed : Nat.card {x : E // J.conj x = x} = 2^n) :
    ∃ κ : E, κ + (fiveForm J).conj κ = 1 :=
  BenderSuzuki.External.huppert_II_10_4_trace_surjective J (2^n) hE hfixed 1 (by simp)

include hE hconj in
/-- The source presentation identifies the whole published model with the
same quotient, preserving both full endpoint subgroups at either orientation. -/
theorem fiveData_model_marking {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    (hZ : center (X ⧸ Q.D) = ⊥)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n) {j : Fin 2}
    (d : FiveData Q split j (fiveForm J)) :
    ∃ (M : GreenBook.UnitaryFive.Model (2^n)) (m : M.Carrier ≃* (X ⧸ Q.D)),
      M.leftParabolic.map m.toMonoidHom = Q.tits.standardParabolic {Q.simple j} ∧
      M.rightParabolic.map m.toMonoidHom = Q.tits.standardParabolic {Q.simple (1-j)} := by
  obtain ⟨κ,hκ⟩ := source_trace_one J n hE hfixed
  obtain ⟨M,f,a,hf,hline,hplane⟩ := small_source_model J n hE hconj
  let q := d.projectiveEquiv (fiveForm J) κ hκ rfl hm hZ
  let m := f.symm.trans q
  have he : m.toMonoidHom.comp f.toMonoidHom = q.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    simp [m]
  refine ⟨M,m,?_,?_⟩
  · rw [←hline,Subgroup.map_map,he]
    exact d.projective_line (fiveForm J) κ hκ rfl hm hZ
  · rw [←hplane,Subgroup.map_map,he]
    exact d.projective_plane (fiveForm J) κ hκ rfl hm hZ

section Marked
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (hm : rotationOrder Q = 4)

include hE h hm in
/-- Source trace and the constructed equations give the entire projective
comparison, scalar kernel and full Borel, with all three endpoint squares. -/
theorem marked_fiveData_comparison
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n) {j : Fin 2}
    (d : FiveData Q split j (fiveForm J)) :
    ∃ (κ : E) (hκ : κ + (fiveForm J).conj κ = 1)
      (f : ProjectiveSpecialUnitaryMatrixGroup (fiveForm J) ≃* (X ⧸ Q.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag (lineParabolic (fiveForm J)) (planeParabolic (fiveForm J)) j)),
      (d.modelHom (fiveForm J) κ hκ rfl).ker = (project (fiveForm J)).ker ∧
      (∀ a, f (project (fiveForm J) a) = d.modelHom (fiveForm J) κ hκ rfl a) ∧
      (lineParabolic (fiveForm J) ⊓ planeParabolic (fiveForm J)).map f.toMonoidHom = Q.tits.B ∧
      (lineParabolic (fiveForm J)).map f.toMonoidHom = Q.tits.standardParabolic {Q.simple j} ∧
      (planeParabolic (fiveForm J)).map f.toMonoidHom = Q.tits.standardParabolic {Q.simple (1-j)} ∧
      (∀ a : parabolic L S 0, (c.left a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm J)) =
        f.symm (mark.left a : X ⧸ Q.D)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm J)) =
          f.symm (mark.middle a : X ⧸ Q.D)) ∧
      (∀ a : parabolic L S 1, (c.right a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm J)) =
        f.symm (mark.right a : X ⧸ Q.D)) := by
  obtain ⟨κ,hκ⟩ := source_trace_one J n hE hfixed
  have hZ := source_center_eq_bot Q mark h split
  refine ⟨κ,hκ,d.projectiveEquiv (fiveForm J) κ hκ rfl hm hZ,
    FiveOriginal.comparison Q mark h split hm (fiveForm J) κ hκ rfl d,
    d.modelHom_kernel (fiveForm J) κ hκ rfl hm hZ,
    d.projectiveEquiv_project (fiveForm J) κ hκ rfl hm hZ,
    d.projective_borel (fiveForm J) κ hκ rfl hm hZ,
    d.projective_line (fiveForm J) κ hκ rfl hm hZ,
    d.projective_plane (fiveForm J) κ hκ rfl hm hZ,
    fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

include hE h in
/-- The same comparison records literal Q.q representatives in both original
endpoints and the whole original overlap. -/
theorem original_fiveData_comparison
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm₀ : rotationOrder Q₀ = 4)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n) {j : Fin 2}
    (d : FiveData Q₀ split₀ j (fiveForm J)) :
    ∃ (f : ProjectiveSpecialUnitaryMatrixGroup (fiveForm J) ≃* ((generated L S) ⧸ Q₀.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag (lineParabolic (fiveForm J)) (planeParabolic (fiveForm J)) j)),
      (lineParabolic (fiveForm J) ⊓ planeParabolic (fiveForm J)).map f.toMonoidHom = Q₀.tits.B ∧
      (∀ a : parabolic L S 0, (c.left a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm J)) =
        f.symm (Q₀.q ⟨a,parabolic_le_generated 0 a.property⟩)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm J)) =
          f.symm (Q₀.q ⟨a,parabolic_le_generated 0 a.property.1⟩)) ∧
      (∀ a : parabolic L S 1, (c.right a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm J)) =
        f.symm (Q₀.q ⟨a,parabolic_le_generated 1 a.property⟩)) := by
  obtain ⟨κ,hκ,f,c,hker,hproject,hB,hline,hplane,hleft,hmiddle,hright⟩ :=
    marked_fiveData_comparison J n hE Q₀ split₀ (originalMarkedIso Q₀) h hm₀ hfixed d
  exact ⟨f,c,hB,
    fun a => by simpa only [originalMarkedIso_left_apply] using hleft a,
    fun a => by simpa only [originalMarkedIso_middle_apply] using hmiddle a,
    fun a => by simpa only [originalMarkedIso_right_apply] using hright a⟩
end Marked

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (h : HypothesisF11 L S) (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso (DGS85.OriginalExtension.reducedAmalgam L S) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 4)

/-- The literal reduced comparison and its three squares, in either endpoint
orientation, are obtained from the source equations on this same quotient. -/
def reducedFiveComparison
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n) (line : Bool)
    (d : FiveData Q split (if line then 0 else 1) (fiveForm J)) :
    UnitarySource.Combined.FiveComparison Q e n line  := Classical.choice (by
  obtain ⟨M,m,hL,hP⟩ := fiveData_model_marking J n hE hconj Q split hm
    (reduced_source_center h Q e split) hfixed d
  let c := MarkedAmalgam.fromSource Q M.leftParabolic M.rightParabolic
    (if line then 0 else 1) m hL hP
  refine ⟨{ model := M, quotient := m.symm, comparison := ?_,
            left_square := ?_, middle_square := ?_, right_square := ?_ }⟩
  · cases line <;> exact e.trans c
  · cases line <;> intro x <;> rfl
  · cases line <;> intro x <;> rfl
  · cases line <;> intro x <;> rfl)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

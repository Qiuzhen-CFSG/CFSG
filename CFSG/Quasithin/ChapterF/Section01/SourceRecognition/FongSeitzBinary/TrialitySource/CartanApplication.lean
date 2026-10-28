module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.CartanActions
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.TorusCharacterAlgebra
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.StructuralApplication

/-!
# Orthogonal source rank-one groups and their Cartan actions

The two root markings and the actual Weyl lifts identify the full images
of the rank-one maps with the canonical R_i in this quotient. Generation by
upper and lower transvections includes q=2 and removes separate rank-one
endpoint placement hypotheses. Both endpoint equations retain Q.q and
Q.endpointEquiv in either orientation.

The four literal 6E(b) subgroup assertions then yield all three full
rank-one commutations in Fong--Seitz II (9.25), with right conjugation and
the source order of factors. Applying the diagonal calculations to the
constructed signedData proves its simple and orthogonal Cartan actions,
including both signs and the third short root's Frobenius shift.

The compatible pinnings, field/module equations and mixed torus equations
remain source obligations. In particular this module does not construct
RankOnePair or EarlierModuleEquations from 6E(b), nor claim recognition.
Source: Fong--Seitz I (6E)(b); II §7, (9.25), (9.31), printed pp.218--219.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource
open PinnedApplication
variable {F : Type*} [Field F] [CharP F 2] {σ : F ≃+* F}
  {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (p : RankOnePair σ (X ⧸ Q.D)) (w : WeylPlacement Q p)
  (shortBase : (p.shortOrbit 0).range = simpleRoot Q split (w.indices 0))
  (longBase : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))

namespace RootGeometry
include shortBase in
/-- The short pinning has precisely the canonical root-generated image. -/
theorem shortMap_range : p.shortMap.range = rankOne Q split (w.indices 0) := by
  rw [sl2_range_eq_root_sup,
    rankOne_eq Q split (w.indices 0) (w.lift 0) (w.simple 0), w.short, ← shortBase]
  change (p.shortOrbit 0).range ⊔
    (p.dihedral.A.toMonoidHom.comp (p.shortOrbit 0)).range =
      (p.shortOrbit 0).range ⊔ rightConjugate (p.shortOrbit 0).range p.dihedral.a
  congr 1
  ext x
  change (∃ t, p.dihedral.A (p.shortOrbit 0 t) = x) ↔
    ∃ t, p.shortOrbit 0 t = p.dihedral.A x
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,(p.dihedral.A_A _).symm⟩
  · rintro ⟨t,ht⟩
    exact ⟨t, by rw [ht, p.dihedral.A_A]⟩

include longBase in
/-- The long pinning has precisely the other canonical root-generated image. -/
theorem longMap_range : p.longMap.range = rankOne Q split (w.indices 1) := by
  rw [sl2_range_eq_root_sup,
    rankOne_eq Q split (w.indices 1) (w.lift 1) (w.simple 1), w.long, ← longBase]
  change (p.longOrbit 0).range ⊔
    (p.dihedral.B.toMonoidHom.comp (p.longOrbit 0)).range =
      (p.longOrbit 0).range ⊔ rightConjugate (p.longOrbit 0).range p.dihedral.b
  congr 1
  ext x
  change (∃ t, p.dihedral.B (p.longOrbit 0 t) = x) ↔
    ∃ t, p.longOrbit 0 t = p.dihedral.B x
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,(p.dihedral.B_B _).symm⟩
  · rintro ⟨t,ht⟩
    exact ⟨t, by rw [ht, p.dihedral.B_B]⟩

variable {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)

include shortBase in
theorem short_word_endpoint :
    ∃ x : P (w.indices 0), Q.q x = (p.signedRoots e).nA 1 ∧
      (Q.endpointEquiv (w.indices 0) x : X ⧸ Q.D) = (p.signedRoots e).nA 1 := by
  apply PinnedApplication.short_word_endpoint Q p e
  rw [shortMap_range Q split p w shortBase]
  exact rankOne_le_parabolic Q split _

include longBase in
theorem long_word_endpoint :
    ∃ x : P (w.indices 1), Q.q x = (p.signedRoots e).nB 1 ∧
      (Q.endpointEquiv (w.indices 1) x : X ⧸ Q.D) = (p.signedRoots e).nB 1 := by
  apply PinnedApplication.long_word_endpoint Q p e
  rw [longMap_range Q split p w longBase]
  exact rankOne_le_parabolic Q split _
end RootGeometry

namespace StructuralApplication
variable (hm : rotationOrder Q = 6)
  (row : StructuralRow Q split (w.indices 0) (w.indices 1))

include shortBase longBase hm row in
/-- The first full rank-one commutation of II (9.25). -/
theorem rankOne_orthogonal_long :
    ⁅rankOne Q split (w.indices 0),
      rightConjugate (rankOne Q split (w.indices 1)) (p.dihedral.a * p.dihedral.b)⁆ = ⊥ := by
  rw [← RootGeometry.shortMap_range Q split p w shortBase,
    ← RootGeometry.longMap_range Q split p w longBase, rightConjugate_mul]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨g,rfl⟩
  apply mem_centralizer_iff.mpr
  intro y hy
  change ∃ h, p.longMap h = p.dihedral.A (p.dihedral.B y) at hy
  obtain ⟨h,hh⟩ := hy
  have he : p.dihedral.B (p.dihedral.A (p.longMap h)) = y := by
    rw [hh, p.dihedral.A_A, p.dihedral.B_B]
  rw [← he]
  exact (p.shortMap_commute_longTail
    (positiveCommutations Q split p w shortBase longBase hm row) g h).symm.eq

include shortBase longBase hm row in
/-- The third commutation of II (9.25), with the two factors interchanged. -/
theorem rankOne_orthogonal_short :
    ⁅rankOne Q split (w.indices 1),
      rightConjugate (rankOne Q split (w.indices 0)) (p.dihedral.b * p.dihedral.a)⁆ = ⊥ := by
  rw [← RootGeometry.longMap_range Q split p w longBase,
    ← RootGeometry.shortMap_range Q split p w shortBase, rightConjugate_mul]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨g,rfl⟩
  apply mem_centralizer_iff.mpr
  intro y hy
  change ∃ h, p.shortMap h = p.dihedral.B (p.dihedral.A y) at hy
  obtain ⟨h,hh⟩ := hy
  have he : p.dihedral.A (p.dihedral.B (p.shortMap h)) = y := by
    rw [hh, p.dihedral.B_B, p.dihedral.A_A]
  rw [← he]
  exact (p.longMap_commute_shortTail
    (positiveCommutations Q split p w shortBase longBase hm row) g h).symm.eq

include shortBase longBase hm row in
/-- The middle commutation of II (9.25), on the same quotient and Weyl lifts. -/
theorem rankOne_orthogonal_middle :
    ⁅rightConjugate (rankOne Q split (w.indices 0)) p.dihedral.b,
      rightConjugate (rankOne Q split (w.indices 1)) p.dihedral.a⁆ = ⊥ := by
  rw [← RootGeometry.shortMap_range Q split p w shortBase,
    ← RootGeometry.longMap_range Q split p w longBase]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  change ∃ g, p.shortMap g = p.dihedral.B x at hx
  change ∃ h, p.longMap h = p.dihedral.A y at hy
  obtain ⟨g,hg⟩ := hx
  obtain ⟨h,hh⟩ := hy
  have he : p.dihedral.B (p.shortMap g) = x := by rw [hg, p.dihedral.B_B]
  have hf : p.dihedral.A (p.longMap h) = y := by rw [hh, p.dihedral.A_A]
  rw [← he, ← hf]
  exact (p.shortMiddle_commute_longMiddle
    (positiveCommutations Q split p w shortBase longBase hm row) g h).symm.eq

local notation "K" => ScalarMarking.SourceFixed (σ := σ)
variable [Finite F] {n : ℕ} {hn : 0 < n}
  (hfaith : Function.Injective p.longMap)
  (e : ScalarMarking (binaryParameters n hn) σ) (θ : F) (hθ : σ θ ≠ θ)
  (d : EarlierModuleEquations p e θ)

/-- The constructed signed source data satisfies both simple short characters. -/
theorem hA_signedSimple (t : Fˣ) (positive : Bool) (a : F) :
    let L := (signedData Q split p w shortBase longBase hm row hfaith e θ hθ d).roots
    L.hA (Units.map e.extension.toMonoidHom t) * L.shortSigned positive 0 (e.extension a) *
      (L.hA (Units.map e.extension.toMonoidHom t))⁻¹ =
    L.shortSigned positive 0
      (e.extension ((if positive then t.val ^ 2 else t.val⁻¹ ^ 2) * a)) :=
  p.hA_signedShort0 e t positive a

/-- The long parameter uses the restriction of the same extension marking. -/
theorem hB_signedSimple (t : Kˣ) (positive : Bool) (a : K) :
    let L := (signedData Q split p w shortBase longBase hm row hfaith e θ hθ d).roots
    L.hB (Units.map e.fixed.toMonoidHom t) * L.longSigned positive 0 (e.fixed a) *
      (L.hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
    L.longSigned positive 0
      (e.fixed ((if positive then t.val ^ 2 else t.val⁻¹ ^ 2) * a)) :=
  p.hB_signedLong0 e t positive a

/-- Structural 6E(b) commutators give the trivial short-coroot character on F. -/
theorem hA_signedOrthogonal (t : Fˣ) (positive : Bool) (a : K) :
    let L := (signedData Q split p w shortBase longBase hm row hfaith e θ hθ d).roots
    L.hA (Units.map e.extension.toMonoidHom t) * L.longSigned positive 2 (e.fixed a) *
      (L.hA (Units.map e.extension.toMonoidHom t))⁻¹ =
    L.longSigned positive 2 (e.fixed a) :=
  p.hA_signedLong2 e (positiveCommutations Q split p w shortBase longBase hm row) t positive a

/-- The trivial long-coroot character preserves D's Frobenius-shifted marking. -/
theorem hB_signedOrthogonal (t : Kˣ) (positive : Bool) (a : F) :
    let L := (signedData Q split p w shortBase longBase hm row hfaith e θ hθ d).roots
    L.hB (Units.map e.fixed.toMonoidHom t) * L.shortSigned positive 2 (e.extension a) *
      (L.hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
    L.shortSigned positive 2 (e.extension a) :=
  p.hB_signedShort2 e (positiveCommutations Q split p w shortBase longBase hm row) t positive a

omit [Finite F] in
include e in
/-- The two rank-one torus words multiply on the source quotient as soon as
their cross-commutation is established.  The field equivalences are used to
transport the rank-one multiplicativity from the original cubic and fixed
fields to the presentation's marked fields. -/
theorem signed_torus_mul_of_cross_commuting
    (hcomm : ∀ s t,
      Commute ((p.signedRoots e).hA s) ((p.signedRoots e).hB t))
    (a b : TorusParameters n hn) :
    (p.signedRoots e).torus (a * b) =
      (p.signedRoots e).torus a * (p.signedRoots e).torus b := by
  apply SignedRoots.torus_mul_of_commute (p.signedRoots e)
  · intro s t
    let s' : Fˣ := Units.map e.extension.symm.toMonoidHom s
    let t' : Fˣ := Units.map e.extension.symm.toMonoidHom t
    have hs' : Units.map e.extension.toMonoidHom s' = s := by
      change Units.map e.extension.toMonoidHom
        (Units.map e.extension.symm.toMonoidHom s) = s
      ext
      simp
    have ht' : Units.map e.extension.toMonoidHom t' = t := by
      change Units.map e.extension.toMonoidHom
        (Units.map e.extension.symm.toMonoidHom t) = t
      ext
      simp
    rw [← hs', ← ht']
    simpa only [map_mul] using p.hA_mul e s' t'
  · intro s t
    let s' : Kˣ := Units.map e.fixed.symm.toMonoidHom s
    let t' : Kˣ := Units.map e.fixed.symm.toMonoidHom t
    have hs' : Units.map e.fixed.toMonoidHom s' = s := by
      change Units.map e.fixed.toMonoidHom
        (Units.map e.fixed.symm.toMonoidHom s) = s
      ext
      simp
    have ht' : Units.map e.fixed.toMonoidHom t' = t := by
      change Units.map e.fixed.toMonoidHom
        (Units.map e.fixed.symm.toMonoidHom t) = t
      ext
      simp
    rw [← hs', ← ht']
    simpa only [map_mul] using p.hB_mul e s' t'
  · exact hcomm

end StructuralApplication
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource

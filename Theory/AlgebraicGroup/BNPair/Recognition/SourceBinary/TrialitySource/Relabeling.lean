module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.Generation
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.RankOneTorus
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.RootParameters

/-!
# Relabeling an entire source rank-one pinning

Precompose the fixed-field SL₂ map with an entrywise field automorphism.
This changes all three long-root parameters, for both signs, together. The
short roots, actual Weyl elements, braid and geometric placements remain
unchanged; the long coroot uses the very same automorphism on units. In
particular this is not an independent reparametrization of one root line.

Source: Fong--Seitz II, printed p.219, the relabeling of all elements of R₁
before (9.27). ScalarAlignment applies this operation after comparing the
two actions in a section of the original quotient's U.
-/


@[expose] public noncomputable section
open Theory.PSL2.SemilinearCoverage
open Theory.PSL2 (sl2FieldAut)
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y] {σ : F ≃+* F}
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
namespace RankOnePair
def relabelLong (p : RankOnePair σ Y) (η : K ≃+* K) : RankOnePair σ Y where
  shortMap := p.shortMap
  longMap := p.longMap.comp (sl2FieldAut η).toMonoidHom
  braid := by simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sl2FieldAut_weyl] using p.braid
  orthogonalShort a := by simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sl2FieldAut_weyl] using p.orthogonalShort a
  orthogonalLong a := by simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sl2FieldAut_weyl, sl2FieldAut_uni] using p.orthogonalLong (η a)

variable (p : RankOnePair σ Y) (η : K ≃+* K)

@[simp] theorem relabelLong_dihedral (p : RankOnePair σ Y) (η : K ≃+* K) : (p.relabelLong η).dihedral = p.dihedral := by
  unfold dihedral relabelLong
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sl2FieldAut_weyl]

@[simp] theorem relabelLong_short (p : RankOnePair σ Y) (η : K ≃+* K) (i : Fin 3) (a : F) :
    (p.relabelLong η).s i a = p.s i a := by
  fin_cases i
  · rfl
  · change (p.relabelLong η).dihedral.B (p.shortMap (uni a)) = p.dihedral.B (p.shortMap (uni a))
    rw [relabelLong_dihedral]
  · change (p.relabelLong η).dihedral.A ((p.relabelLong η).dihedral.B (p.shortMap (uni a))) =
      p.dihedral.A (p.dihedral.B (p.shortMap (uni a)))
    rw [relabelLong_dihedral]

@[simp] theorem relabelLong_long (p : RankOnePair σ Y) (η : K ≃+* K) (i : Fin 3) (a : K) :
    (p.relabelLong η).l i a = p.l i (η a) := by
  have h (a : K) : (p.relabelLong η).l 0 a = p.l 0 (η a) := by
    change p.longMap (sl2FieldAut η (uni a)) = p.longMap (uni (η a))
    rw [sl2FieldAut_uni]
  fin_cases i
  · exact h a
  · change (p.relabelLong η).dihedral.A ((p.relabelLong η).l 0 a) = p.dihedral.A (p.l 0 (η a))
    rw [relabelLong_dihedral,h]
  · change (p.relabelLong η).dihedral.B ((p.relabelLong η).dihedral.A ((p.relabelLong η).l 0 a)) =
      p.dihedral.B (p.dihedral.A (p.l 0 (η a)))
    rw [relabelLong_dihedral,h]

@[simp] theorem relabelLong_short_range (p : RankOnePair σ Y) (η : K ≃+* K) (i : Fin 3) :
    ((p.relabelLong η).shortOrbit i).range = (p.shortOrbit i).range := by
  have he : (p.relabelLong η).shortOrbit i = p.shortOrbit i := by
    apply MonoidHom.ext
    intro a
    exact p.relabelLong_short η i a.toAdd
  exact congrArg MonoidHom.range he

@[simp] theorem relabelLong_long_range (p : RankOnePair σ Y) (η : K ≃+* K) (i : Fin 3) :
    ((p.relabelLong η).longOrbit i).range = (p.longOrbit i).range := by
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨.ofAdd (η a.toAdd), p.relabelLong_long η i a.toAdd |>.symm⟩
  · rintro ⟨a,rfl⟩
    refine ⟨.ofAdd (η.symm a.toAdd), ?_⟩
    change (p.relabelLong η).l i (η.symm a.toAdd) = p.l i a.toAdd
    rw [relabelLong_long,η.apply_symm_apply]

@[simp] theorem relabelLong_longMap_range (p : RankOnePair σ Y) (η : K ≃+* K) : (p.relabelLong η).longMap.range = p.longMap.range := by
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨sl2FieldAut η a,rfl⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨b,rfl⟩ := (sl2FieldAut η).surjective a
    exact ⟨b,rfl⟩

@[simp] theorem relabelLong_signedValue (p : RankOnePair σ Y) (η : K ≃+* K) (positive : Bool) (z : Y) :
    (p.relabelLong η).signedValue positive z = p.signedValue positive z := by
  simp only [signedValue, relabelLong_dihedral]

variable {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)

theorem relabelLong_signedShort (p : RankOnePair σ Y) (η : K ≃+* K) (positive : Bool) (i : Fin 3) (a : F) :
    ((p.relabelLong η).signedRoots e).shortSigned positive i (e.extension a) =
      (p.signedRoots e).shortSigned positive i (e.extension a) := by
  rw [signedRoots_short, signedRoots_short, relabelLong_signedValue]
  congr 1
  fin_cases i
  · exact p.relabelLong_short η 0 a
  · exact p.relabelLong_short η 1 a
  · exact p.relabelLong_short η 2 (σ a)

theorem relabelLong_signedLong (p : RankOnePair σ Y) (η : K ≃+* K) (positive : Bool) (i : Fin 3) (a : K) :
    ((p.relabelLong η).signedRoots e).longSigned positive i (e.fixed a) =
      (p.signedRoots e).longSigned positive i (e.fixed (η a)) := by
  rw [signedRoots_long, signedRoots_long, relabelLong_signedValue,relabelLong_long]

omit [CharP F 2] in
private theorem fieldAut_tor (η : K ≃+* K) (a : Kˣ) :
    sl2FieldAut η (tor a) = tor (Units.map η.toMonoidHom a) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change η ((tor a).val i j) = (tor (Units.map η.toMonoidHom a)).val i j
  fin_cases i <;> fin_cases j <;> simp [tor]

theorem relabelLong_hB (p : RankOnePair σ Y) (η : K ≃+* K) (a : Kˣ) :
    ((p.relabelLong η).signedRoots e).hB (Units.map e.fixed.toMonoidHom a) =
      (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom (Units.map η.toMonoidHom a)) := by
  rw [hB_parameter,hB_parameter]
  change p.longMap (sl2FieldAut η (tor a)) = _
  rw [fieldAut_tor]

end RankOnePair
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
  (p : RankOnePair σ (X ⧸ Q.D)) (w : WeylPlacement Q p) (η : K ≃+* K)

def WeylPlacement.relabelLong (Q : MarkedQuotient P)
    (p : RankOnePair σ (X ⧸ Q.D)) (w : WeylPlacement Q p) (η : K ≃+* K) : WeylPlacement Q (p.relabelLong η) where
  indices := w.indices
  lift := w.lift
  short := by simpa only [RankOnePair.relabelLong_dihedral] using w.short
  long := by simpa only [RankOnePair.relabelLong_dihedral] using w.long
  simple := w.simple

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource

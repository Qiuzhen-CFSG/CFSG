module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.LinearCoefficientEquiv
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Transport of the L₅(2) parabolic residual

The field of order two is identified with F₂ by coefficient transport;
the projective quotient is then identified with its natural linear action.
The same ambient equivalence carries the actual subgroup, its intrinsic
two-core quotient, and the embedded solvable residual of its parabolic.
Sylow normalizers are transported with the parabolic. The artificial top
subgroup in `IsParabolicResidual A ⊤ false` is removed by its canonical
isomorphism, preserving the specified residual image.

These transport facts do not identify that image with an end parabolic.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.12(5),
printed pp.47–48, and the proof of 1.3.9, printed p.514.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.LinearFiveStabilizer
open BinaryLinear.OuterCyclic
variable {G Q : Type*} [Group G] [Group Q]

/-- Coefficient transport keeps the actual projective matrix model. -/
noncomputable def binaryFiveEquiv (hQ : ClassicalGroup.IsPSL Q 5 2) : Q ≃* LinearGroup 5 := by
  apply Classical.choice
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hQ
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact ⟨e.trans ((Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF).trans
    (projectiveEquivLinear (by decide)))⟩

/-- The Sylow-normalizer Borel is transported with the parabolic. -/
theorem lieParabolicTwo_map [Finite G] {P : Subgroup G}
    (hP : Section02.LieParabolicTwo P) (e : G ≃* Q) :
    Section02.LieParabolicTwo (P.map e.toMonoidHom) := by
  obtain ⟨T, hT⟩ := hP
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change normalizer (↑((T : Subgroup G).map e.toMonoidHom) : Set Q) ≤ _
  rw [← map_equiv_normalizer_eq]
  exact map_mono hT

/-- The image of a solvable residual is the residual of the actual image. -/
theorem embeddedResidual_map [Finite G] (P : Subgroup G) (e : G ≃* Q) :
    ((solvableResidual P).map P.subtype).map e.toMonoidHom =
      (solvableResidual (P.map e.toMonoidHom)).map (P.map e.toMonoidHom).subtype := by
  let f : P ≃* (P.map e.toMonoidHom) := e.subgroupMap P
  have hc : (P.map e.toMonoidHom).subtype.comp f.toMonoidHom =
      e.toMonoidHom.comp P.subtype := rfl
  have he : (solvableResidual P).map f.toMonoidHom =
      solvableResidual (P.map e.toMonoidHom) :=
    map_solvableResidual_eq f.toMonoidHom f.surjective
  rw [← he]
  simp only [map_map, hc]

/-- Remove only the artificial top subgroup in the source embedding convention. -/
theorem exists_parabolic_of_top_residual [Finite G] {A : Subgroup G}
    (hA : Section02.IsParabolicResidual A ⊤ false) :
    ∃ P : Subgroup G, Section02.LieParabolicTwo P ∧
      (solvableResidual P).map P.subtype = A := by
  obtain ⟨P, hP, _, he⟩ := hA
  let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  refine ⟨P.map e.toMonoidHom, lieParabolicTwo_map hP e, ?_⟩
  rw [← embeddedResidual_map P e, map_map]
  exact he

/-- The intrinsic two-core quotient is carried along the subgroup isomorphism. -/
theorem isPSL_twoQuotient_map {A : Subgroup G} {n q : ℕ}
    (hA : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) n q) (e : G ≃* Q) :
    ClassicalGroup.IsPSL ((A.map e.toMonoidHom) ⧸ pCore 2 (A.map e.toMonoidHom)) n q := by
  let f := e.subgroupMap A
  let fQ := QuotientGroup.congr (pCore 2 A) (pCore 2 (A.map e.toMonoidHom)) f
    (pCore_map_iso 2 f)
  exact hA.of_mulEquiv fQ.symm

/-- Both source hypotheses survive the concrete linear identification. -/
theorem linear_model_residual [Finite Q] (hQ : ClassicalGroup.IsPSL Q 5 2)
    {A : Subgroup Q} (hA : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2)
    (hres : Section02.IsParabolicResidual A ⊤ false) :
    let e := binaryFiveEquiv hQ
    ClassicalGroup.IsPSL ((A.map e.toMonoidHom) ⧸ pCore 2 (A.map e.toMonoidHom)) 4 2 ∧
      ∃ P : Subgroup (LinearGroup 5), Section02.LieParabolicTwo P ∧
        (solvableResidual P).map P.subtype = A.map e.toMonoidHom := by
  dsimp only
  let e := binaryFiveEquiv hQ
  refine ⟨isPSL_twoQuotient_map hA e, ?_⟩
  obtain ⟨P, hP, he⟩ := exists_parabolic_of_top_residual hres
  refine ⟨P.map e.toMonoidHom, lieParabolicTwo_map hP e, ?_⟩
  rw [← embeddedResidual_map P e, he]

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.LinearFiveStabilizer

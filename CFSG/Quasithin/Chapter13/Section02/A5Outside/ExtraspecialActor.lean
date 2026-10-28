module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.CoreKernel
public import CFSG.Quasithin.ChapterE.Section02.SolvableStructure.ExtraspecialActor
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.WreathThompson
import all CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.WreathActor
/-!
# The extraspecial branch on the original outside omega orbit

The original canonical core equals C_H(U), with U the actual omega-center
orbit. Its full natural action supplies the exact S₃/wreath quotient.
E.2.1 and nontrivial X=O²(C_H(U)) now yield the actual cyclic-four image
of R=O₂(XT), together with R∩C_H(U)=O₂(H).

The second consumer retains X in the original ambient G, discharges the
cyclic-four and kernel hypotheses of the Thompson theorem, and concludes
H≤N_G(J(R)). Only the original escape produced by the preceding R-even
argument remains explicit; it is owned by the 13.2.9 source assembly.

Source: Aschbacher–Smith, original 13.2.9, printed pp.880–881.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]
/-- The actual source residual produces the cyclic-four image and exact
centralizer intersection; neither is an assumed model premise. -/
theorem source_residual_kernel_cyclicFour
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    let h := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    let C := centralizer (U : Set H)
    let X := (pResidual 2 C).map C.subtype
    let R := (X ⊔ (S : Subgroup H)).pCoreIn 2
    let q := QuotientGroup.mk' C
    pResidual 2 C ≠ ⊥ →
    (¬ (ChapterB.minimalParabolicMax S h.2.2.1).pCoreIn 2 ≤ pCore 2 H ∨
      ¬ centralizerModulo (S : Subgroup H) (ChapterB.minimalParabolicCore S h.2.2.1)
        ((ChapterB.minimalParabolicCore S h.2.2.1).pCoreIn 2) ≤ pCore 2 H) →
    pCore 2 H ≤ R ∧ pCore 2 H = R ⊓ C ∧ IsCyclic (R.map q) ∧ Nat.card (R.map q) = 4 := by
  let h := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  have hJC : ChapterB.minimalParabolicCore S h.2.2.1 = C := source_core_eq_omega_centralizer d hH hB hZ hs
  dsimp only
  intro hne hescape
  have hne' : pResidual 2 (ChapterB.minimalParabolicCore S h.2.2.1) ≠ ⊥ := by rwa [hJC]
  have ha : Nonempty ((H ⧸ ChapterB.minimalParabolicCore S h.2.2.1) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∨
      Nonempty ((H ⧸ ChapterB.minimalParabolicCore S h.2.2.1) ≃*
        RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))) := by
    have hw := source_solvable_wreath_omega_action d hH hB hZ hs
    rcases hw with ⟨c,e,he⟩ | ⟨e,c,he⟩
    · exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq hJC).trans e⟩
    · exact Or.inr ⟨(QuotientGroup.quotientMulEquivOfEq hJC).trans e⟩
  have hh := ChapterE.SolvableMinimalParabolic.source_cyclicFour_image h.1 S h.2.2.1 hs hescape hne' ha
  let F (N : {J : Subgroup H // J.Normal}) : Prop :=
    letI := N.property
    let X := (pResidual 2 N.val).map N.val.subtype
    let R := (X ⊔ (S : Subgroup H)).pCoreIn 2
    let q := QuotientGroup.mk' N.val
    pCore 2 H ≤ R ∧ pCore 2 H = R ⊓ N.val ∧ IsCyclic (R.map q) ∧ Nat.card (R.map q) = 4
  have heq : (⟨ChapterB.minimalParabolicCore S h.2.2.1,inferInstance⟩ :
      {J : Subgroup H // J.Normal}) = ⟨C,inferInstance⟩ := Subtype.ext hJC
  have hh' : F ⟨ChapterB.minimalParabolicCore S h.2.2.1,inferInstance⟩ := hh
  have hc : F ⟨C,inferInstance⟩ := heq ▸ hh'
  exact hc
/-- In the genuine nontrivial residual branch, H normalizes the ambient
Thompson subgroup of the original R=O₂(XT). -/
theorem source_residual_kernel_thompson
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    let h := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    let C := centralizer (U : Set H)
    let X := (pResidual 2 C).map C.subtype
    let R := (X ⊔ (S : Subgroup H)).pCoreIn 2
    X.map H.subtype ≠ ⊥ →
    (¬ (ChapterB.minimalParabolicMax S h.2.2.1).pCoreIn 2 ≤ pCore 2 H ∨
      ¬ centralizerModulo (S : Subgroup H) (ChapterB.minimalParabolicCore S h.2.2.1)
        ((ChapterB.minimalParabolicCore S h.2.2.1).pCoreIn 2) ≤ pCore 2 H) →
    ChapterB.thompsonJ R 0 = ChapterB.thompsonJ (pCore 2 H) 0 ∧
      (ChapterB.thompsonJ R 0).Normal ∧
      H ≤ normalizer (ChapterB.thompsonJ (R.map H.subtype) 0 : Set G) := by
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let X := (pResidual 2 C).map C.subtype
  let R := (X ⊔ (S : Subgroup H)).pCoreIn 2
  dsimp only
  intro hX hescape
  have hne : pResidual 2 C ≠ ⊥ := by
    intro hh
    apply hX
    change ((pResidual 2 C).map C.subtype).map H.subtype = ⊥
    rw [hh,Subgroup.map_bot,Subgroup.map_bot]
  obtain ⟨hQR,hcore,hcyclic,hcard⟩ :=
    source_residual_kernel_cyclicFour d hH hB hZ hs hne hescape
  exact source_cyclicFour_thompson d hH hB hZ hs R hQR hcore hcyclic hcard
end CFSG.Quasithin.Chapter13.Section02.A5Outside

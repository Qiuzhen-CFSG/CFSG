module

public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.Source
public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.Placement
public import Theory.GroupTheory.CenterlessSupplementCentralizer
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient

/-!
# Long-root placement from the original corefree minimal parabolic

The original maximal subgroup's trivial normal core kills O₂(H). The normal
simple PSL₃ subgroup is centerless, and the Sylow supplement makes its quotient
a two-group, so its ambient centralizer is trivial. The actual elementary
normal subgroup can therefore be fed into the faithful geometric placement
calculation. Neither innerness, graph action nor root containment is assumed.

Source: Aschbacher--Smith, E.2.7, printed p.219.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.MinimalParabolicWitness Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.ChapterE.Structure.LinearThree
open ChapterB
variable {H : Type*} [Group H] [Finite H]
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
variable (K : Subgroup H) [K.Normal] [IsSimpleGroup K]
variable (e : K ≃* PSL(3,F)) (T : Sylow 2 H)

include e in
omit [Finite H] [Finite F] [CharP F 2] in
/-- The corefree hypotheses imply faithful conjugation on the normal matrix group. -/
theorem centralizer_eq_bot (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : IsMinimalParabolicOver T ⊤)
    (hcore : (minimalParabolicMax T hP).normalCore = ⊥) :
    centralizer (K : Set H) = ⊥ := by
  have htwo : pCore 2 H = ⊥ := by
    apply bot_unique
    have hh : pCore 2 H ≤ minimalParabolicMax T hP :=
      pCore_isPGroup.le_sylow_of_normal T |>.trans (minimalParabolicMax_spec T hP).2
    exact (normal_le_normalCore.mpr hh).trans hcore.le
  let : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Theory.GroupTheory.centralizer_eq_bot_of_simple_two_quotient K
    (Group.IsPerfect.not_isMulCommutative K)
    (isPGroup_quotient_of_sup_eq_top K (T : Subgroup H) T.isPGroup' hgen) htwo

include hn hF in
/-- E.2.7's long-root placement retains the original elementary subgroup V.
Its normality in T suffices; the additional source containment V≤O₂(M) is
available to consumers but is not needed for this branch's geometry. -/
theorem exists_longRoot_placement (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : IsMinimalParabolicOver T ⊤)
    (hcore : (minimalParabolicMax T hP).normalCore = ⊥)
    (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ (T : Subgroup H)) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) :
    ∃ g : PSL(3,F),
      let e' := e.trans (MulAut.conj g)
      (T : Subgroup H).comap (modelEmbedding F K e') = unipotent F ∧
      (minimalParabolicMax T hP).comap (modelEmbedding F K e') = borel F ∧
      V ≤ (projectiveCenter F).map (modelEmbedding F K e') := by
  obtain ⟨g,hU,_,hB⟩ := exists_diagram_and_borel F hn hF K e T hgen hP
  refine ⟨g,hU,hB, ?_⟩
  exact elementary_le_longRoot F K _ hn hF (T : Subgroup H) (minimalParabolicMax T hP)
    V hgen hU hP.1 ⟨(minimalParabolicMax_spec T hP).2,(minimalParabolicMax_spec T hP).1⟩
    (centralizer_eq_bot F K e T hgen hP hcore) hVT hVN

end CFSG.Quasithin.ChapterE.Structure.LinearThree

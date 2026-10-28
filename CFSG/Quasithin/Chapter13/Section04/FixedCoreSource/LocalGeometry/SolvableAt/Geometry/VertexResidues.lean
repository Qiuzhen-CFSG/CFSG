module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.VertexResidues
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SixLetterPair
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalPlane
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAction

/-!
# Quotients and residues of the original solvable vertices: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/Geometry/VertexResidues` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3 Quasithin.I5
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- The first-vertex residue is constructed from the literal centralizer
and inside plane normalizer, using the actual six-letter quotient. -/
theorem original_point_parabolics_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hinter : centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G))
    (B : Subgroup G) (hBM : B ≤ normalizer (L : Set G)) (hTB : (T : Subgroup G) ≤ B)
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hB : IsCoatom (B.subgroupOf (normalizer (L : Set G))))
    (hgen : (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G)) :
    let M := normalizer (L : Set G)
    Quasithin.I5.RankTwoParabolics M ((T : Subgroup G).subgroupOf M)
      ((centralizer ({z.val} : Set G)).subgroupOf M) (B.subgroupOf M) := by
  let M := normalizer (L : Set G)
  let A := centralizer ({z.val} : Set G) ⊓ M
  let Ai := (centralizer ({z.val} : Set G)).subgroupOf M
  let Bi := B.subgroupOf M
  let S := T.subtype D.sylow_normalizes_component
  have hTA : (T : Subgroup G) ≤ A :=
    le_inf (original_sylow_le_centralizer hz) D.sylow_normalizes_component
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup
  obtain ⟨eA⟩ := normalizer_centralizer_quotient D m hcore z hzL hinter
  let a : Ai ≃* A :=
    (MulEquiv.subgroupCongr (inf_subgroupOf_right _ _).symm).trans
      (subgroupOfEquivOfLe (show A ≤ M from inf_le_right))
  have ha : ¬ IsPGroup 2 Ai := fun hp =>
    not_twoGroup_of_symmetricThree_quotient eA (hp.of_equiv a)
  let b := subgroupOfEquivOfLe hBM
  have hb : ¬ IsPGroup 2 Bi := fun hp =>
    not_twoGroup_of_symmetricThree_quotient eB (hp.of_equiv b)
  have hSA : (S : Subgroup M) ≤ Ai := fun _ hx => (hTA hx).1
  have hSB : (S : Subgroup M) ≤ Bi := fun _ hx => hTB hx
  have hAp : Ai ≠ ⊤ := by
    intro he
    apply hzL
    intro l hl
    exact mem_centralizer_singleton_iff.mp
      (show (⟨l,L.le_normalizer hl⟩ : M) ∈ Ai from he ▸ mem_top _)
  have hne : Ai ≠ Bi := by
    intro he
    have hAB : A = B := by
      have hh := congrArg (map M.subtype) he
      rwa [subgroupOf_map_subtype,map_subgroupOf_eq_of_le hBM] at hh
    have hgen' : A ⊔ B = M := hgen
    have hBtop : B = M := by simpa only [hAB,sup_idem] using hgen'
    exact hB.ne_top (by change B.subgroupOf M = ⊤; rw [hBtop,subgroupOf_self])
  exact Quasithin.I5.RankTwoParabolics.of_six_letter_two_quotient (pCore 2 M) pCore_isPGroup
    (LocalGeometry.normalizer_quotient_of_ordinary_at h structural D m eL hM) S Ai Bi
    (lt_iff_le_not_ge.mpr ⟨hSA,fun hh => ha (S.isPGroup'.to_le hh)⟩)
    (lt_iff_le_not_ge.mpr ⟨hSB,fun hh => hb (S.isPGroup'.to_le hh)⟩)
    hAp hB.ne_top hne


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

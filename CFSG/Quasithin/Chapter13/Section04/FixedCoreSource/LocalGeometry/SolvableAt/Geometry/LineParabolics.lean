module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.CoveredPlacement
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.CoveredSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.FirstFlagCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.LineParabolics
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredSelection
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SymmetricThreePair
public import Theory.GroupTheory.SylowNormalizedResidual
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The original solvable line residue: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/Geometry/LineParabolics` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem original_R1_line_parabolics_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore_at h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore_at h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
    let P := I ⊔ (T : Subgroup G)
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Quasithin.I5.RankTwoParabolics H ((T : Subgroup G).subgroupOf H)
        ((normalizer (L : Set G)).subgroupOf H) (P.subgroupOf H) ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
  obtain ⟨ordinary,_,hI,_,hprod,hinter,_,hstar,_⟩ := centralizer_pair_quotient_of_original_R1_at
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  obtain ⟨eL⟩ := ordinary
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup
  have hRT := (firstFlagCore_local_data_at h structural D m z hz hzL).1
  exact ⟨⟨eL⟩,centralizer_rankTwo_of_source_product D m hcore z hzL hz
    (firstFlagCore_at h structural D m) hRT hI hprod hinter hout,
    thompson_sylow_join_quotient hz (firstFlagCore_at h structural D m) hRT hI,hstar⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

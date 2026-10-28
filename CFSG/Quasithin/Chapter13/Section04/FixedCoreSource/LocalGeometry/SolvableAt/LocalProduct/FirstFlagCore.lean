module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FirstFlagNormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.FirstParabolicAction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.FirstParabolicCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstFlagCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstFlagNormalizer
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstParabolicAction

/-!
# The original R₁ in the solvable local product: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/FirstFlagCore` proof for the local step.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Conjugation on V by the source normalizer N_LT(V₁). -/
def firstFlagAction_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    firstFlagNormalizer T L V →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion
    ((inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
      (normalizer_component_le_module_at h structural D m)))

/-- The original R₁: the preimage in T of O₂ of M₁'s action on V. -/
def firstFlagCore_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) : Subgroup G :=
  ((pCore 2 (firstFlagAction_at h structural D m).range).comap
    ((firstFlagAction_at h structural D m).rangeRestrict.comp
      (inclusion sylow_le_firstFlagNormalizer))).map (T : Subgroup G).subtype

private def coreAt_at (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
    (hPV : P ≤ normalizer (V : Set G)) : Subgroup G :=
  let f := V.normalizerMonoidHom.comp (inclusion hPV)
  ((pCore 2 f.range).comap (f.rangeRestrict.comp (inclusion hTP))).map
    (T : Subgroup G).subtype

/-- The original R₁ and the previously checked literal residual action core coincide. -/
theorem firstFlagCore_eq_firstActionCore_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    firstFlagCore_at h structural D m = firstActionCore_at h structural D m z.val := by
  have he := LocalGeometry.first_flag_normalizer_eq_firstResidual_sylow_at h structural D m e z hz hzL
  change firstFlagNormalizer T L V = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) at he
  change coreAt_at (firstFlagNormalizer T L V) _ _ =
    coreAt_at (firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) _ _
  congr 1

/-- In the ordinary row the original R₁ is exactly O₂(L₁T). -/
theorem firstFlagCore_eq_firstParabolicCore_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    firstFlagCore_at h structural D m = firstParabolicCore T L z.val :=
  (firstFlagCore_eq_firstActionCore_at h structural D m e z hz hzL).trans
    (firstActionCore_eq_firstParabolicCore_at h structural D m e hz)

/-- Apply the short-block product theorem to the literal action-core preimage. -/
theorem centralizer_pair_quotient_of_short_block_original_R1_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
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
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z.val ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ∧
      (H : Set G) = (firstCentralizerResidual L z.val : Set G) * (I : Set G) * (T : Set G) ∧
      I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ H →
        (Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ↔
          Y = I ⊔ (T : Subgroup G)) := by
  obtain ⟨e⟩ := ordinary_of_short_core_marking D m hb
  have hR := firstFlagCore_eq_firstParabolicCore_at h structural D m e z hz hzL
  generalize hRa : firstFlagCore_at h structural D m = R at hVJ ⊢
  have hRc : R = firstParabolicCore T L z.val := hRa.symm.trans hR
  clear hRa hR
  subst R
  exact centralizer_pair_quotient_of_short_block_firstParabolicCore_at
    h₀ h structural D m hb z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

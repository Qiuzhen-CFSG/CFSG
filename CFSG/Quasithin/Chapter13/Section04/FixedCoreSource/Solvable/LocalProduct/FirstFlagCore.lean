module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstFlagNormalizer
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstParabolicAction

/-!
# The original R₁ in the solvable local product

Construct M₁=N_LT(V₁) and its literal conjugation action on V. The preimage
in the original T of the action image's two-core is exactly the R₁ of
Notation13.2.1. In the ordinary row, FirstFlagNormalizer identifies M₁
with L₁T. This identifies its two-residual with the original
O^{3′}(C_L(z)) and its action-core preimage with O₂(L₁T).

The short-block consumer now uses this original R₁ in both action-kernel
cases. It retains the genuine earlier V≤J(R₁), fusion, 13.3.9 and
13.4.2–3 inputs. It assumes no local product, quotient, residual-section
Sylow witness or R₁ placement. OrdinaryOriginal also assembles the
ordinary Baumann-bound branch. Covered-row placement, C₃ geometry and
ambient fusion remain with
qt-d-1341-solvable-source; earlier-source discharge remains with
qt-d-1341-fixed-core-source and its producers.
Source: Aschbacher–Smith13.2.1, 13.4.8, pp.877,904–905.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original M₁ of Notation 13.2.1, formed from the Sylow-fixed plane. -/
def firstFlagNormalizer (T : Sylow 2 G) (L V : Subgroup G) : Subgroup G :=
  (L ⊔ (T : Subgroup G)) ⊓ normalizer ((V ⊓ omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) : Set G)

omit [Finite G] in
theorem sylow_le_firstFlagNormalizer : (T : Subgroup G) ≤ firstFlagNormalizer T L V := by
  apply le_inf le_sup_right
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro t ht v hv
  exact (((mem_omegaOneCenterAmbient_iff _ _).mp hv.2).2.2 t ht).symm

/-- Conjugation on V by the source normalizer N_LT(V₁). -/
def firstFlagAction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    firstFlagNormalizer T L V →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion
    ((inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
      (normalizer_component_le_module h structural D m)))

/-- The original R₁: the preimage in T of O₂ of M₁'s action on V. -/
def firstFlagCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) : Subgroup G :=
  ((pCore 2 (firstFlagAction h structural D m).range).comap
    ((firstFlagAction h structural D m).rangeRestrict.comp
      (inclusion sylow_le_firstFlagNormalizer))).map (T : Subgroup G).subtype

private def coreAt (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
    (hPV : P ≤ normalizer (V : Set G)) : Subgroup G :=
  let f := V.normalizerMonoidHom.comp (inclusion hPV)
  ((pCore 2 f.range).comap (f.rangeRestrict.comp (inclusion hTP))).map
    (T : Subgroup G).subtype

/-- The original two-residual definition of L₁ agrees with O^{3′}(C_L(z)). -/
theorem firstFlagNormalizer_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    (pResidual 2 (firstFlagNormalizer T L V)).map (firstFlagNormalizer T L V).subtype =
      firstCentralizerResidual L z.val := by
  have he := first_flag_normalizer_eq_firstResidual_sylow h structural D m e z hz hzL
  change firstFlagNormalizer T L V = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) at he
  rw [he]
  exact embedded_pResidual_join_pGroup _ _ (firstCentralizerResidual_twoPerfect L z.val)
    T.isPGroup' (firstCentralizerResidual_sylow_normalizes D hz)

/-- The original R₁ and the previously checked literal residual action core coincide. -/
theorem firstFlagCore_eq_firstActionCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    firstFlagCore h structural D m = firstActionCore h structural D m z.val := by
  have he := first_flag_normalizer_eq_firstResidual_sylow h structural D m e z hz hzL
  change firstFlagNormalizer T L V = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) at he
  change coreAt (firstFlagNormalizer T L V) _ _ =
    coreAt (firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) _ _
  congr 1

/-- In the ordinary row the original R₁ is exactly O₂(L₁T). -/
theorem firstFlagCore_eq_firstParabolicCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    firstFlagCore h structural D m = firstParabolicCore T L z.val :=
  (firstFlagCore_eq_firstActionCore h structural D m e z hz hzL).trans
    (firstActionCore_eq_firstParabolicCore h structural D m e hz)

/-- Apply the short-block product theorem to the literal action-core preimage. -/
theorem centralizer_pair_quotient_of_short_block_original_R1
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m))
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
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
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
  have hR := firstFlagCore_eq_firstParabolicCore h structural D m e z hz hzL
  generalize hRa : firstFlagCore h structural D m = R at hVJ ⊢
  have hRc : R = firstParabolicCore T L z.val := hRa.symm.trans hR
  clear hRa hR
  subst R
  exact centralizer_pair_quotient_of_short_block_firstParabolicCore
    h₀ h structural D m hb z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

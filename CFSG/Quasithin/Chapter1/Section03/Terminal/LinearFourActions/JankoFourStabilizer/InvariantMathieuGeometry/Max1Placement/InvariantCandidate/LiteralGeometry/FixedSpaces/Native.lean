module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.FixedSpaces.Binary
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.Bounds
import all Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryKernel.Translations
import all Theory.Mathieu.M24.LocalGeometry.LinearFourCore

/-!
# Fixed masks for the native octad translations

The pointwise kernel of the seed octad is exactly its intrinsic two-core:
its order is sixteen and its octad-action quotient is A₈. The native heptad
translation equivalence enumerates all its elements. Extending their actual
23-point permutations and undoing the certified star relabeling gives the
columns of their action on the literal max1 kernel.

The Lean kernel checks these columns against the native permutations and
counts all 2048 masks. Each nonidentity translation fixes exactly 128 masks;
the first two translations have 64 common fixed masks. No splitting of the
max1 extension is used.

The two `import all` edges intentionally access the implementation bodies
of the native permutation and its octad lift for this internal certificate.
They leave the shared modules and their public boundaries unchanged.

Source: the E₂¹¹.M₂₄ subgroup of GLS3 Table 5.3i, used in
Aschbacher–Smith A.3.12(17) and the proof of 1.3.9. The concrete data come
from the certified heptad translations and ATLAS star-coordinate labels.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
open Sporadic.Mathieu.M24LocalGeometry
open Janko4.Cardinality.QuotientCount.Image
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.LiteralBinary

@[expose] def translationVector (n : Fin 16) : Fin 4 → ZMod 2 :=
  fun i => if n.val.testBit i.val then 1 else 0

theorem translationVector_surjective : Function.Surjective translationVector := by
  decide +kernel

private def embed23 (j : Fin 23) : Fin 24 :=
  if j = 0 then 23 else j.castLE (by decide)

private def project23 (i : Fin 24) : Fin 23 :=
  ⟨i.val % 23, Nat.mod_lt _ (by decide)⟩

private def nativePermMap (n : Fin 16) (i : Fin 24) : Fin 24 :=
  if i = 0 then 0 else
    embed23 (heptadBinaryPermutation (translationVector n) (project23 i))

private theorem nativePermMap_involutive : ∀ n : Fin 16,
    Function.Involutive (nativePermMap n) := by
  change ∀ n i, nativePermMap n (nativePermMap n i) = i
  decide +kernel

/-- The native heptad translations extended to the 24-point action. -/
def nativePerm (n : Fin 16) : Equiv.Perm (Fin 24) where
  toFun := nativePermMap n
  invFun := nativePermMap n
  left_inv := nativePermMap_involutive n
  right_inv := nativePermMap_involutive n

private theorem nativePerm_embedded : ∀ (n : Fin 16) (j : Fin 23),
    nativePerm n (m23PointEmbedding j) =
      m23PointEmbedding (heptadBinaryPermutation (translationVector n) j) := by
  simp_rw [m23PointEmbedding_apply]
  decide +kernel

private theorem point_cases : ∀ i : Fin 24,
    i = 0 ∨ ∃ j : Fin 23, m23PointEmbedding j = i := by
  simp_rw [m23PointEmbedding_apply]
  decide +kernel

/-- The enumerated translations as elements of the actual native Mathieu group. -/
noncomputable def nativeTranslation (n : Fin 16) : M24 :=
  (LinearFourCore.kernelEquiv
    (heptadBinaryEquiv (Multiplicative.ofAdd (translationVector n)))).val.val

theorem nativeTranslation_coe (n : Fin 16) :
    (nativeTranslation n : Equiv.Perm (Fin 24)) = nativePerm n := by
  change ((LinearFourCore.heptadLift
    (heptadBinaryEquiv (Multiplicative.ofAdd (translationVector n))).val : M24) :
      Equiv.Perm (Fin 24)) = _
  rw [LinearFourCore.heptadLift_coe]
  apply Equiv.ext
  intro i
  rcases point_cases i with rfl | ⟨j, rfl⟩
  · exact m23ExtendHom_apply_24 _
  · rw [m23ExtendHom_apply_embedded, heptadBinaryEquiv_coe, nativePerm_embedded]
    rfl

theorem seed_core_eq_kernel :
    pCore 2 (octadStabilizer LinearFourCore.seedOctad) =
      (LinearFourCore.action LinearFourCore.seedOctad).ker := by
  apply le_antisymm LinearFourCore.core_le_kernel
  exact le_sSup ⟨inferInstance,
    IsPGroup.of_card (n := 4) LinearFourCore.kernel_card⟩

theorem nativeTranslation_mem (n : Fin 16) :
    nativeTranslation n ∈ (octadStabilizer LinearFourCore.seedOctad).pCoreIn 2 := by
  rw [pCoreIn, seed_core_eq_kernel]
  exact mem_map_of_mem _ (LinearFourCore.kernelEquiv
    (heptadBinaryEquiv (Multiplicative.ofAdd (translationVector n)))).property

theorem nativeTranslation_surjective {g : M24}
    (hg : g ∈ (octadStabilizer LinearFourCore.seedOctad).pCoreIn 2) :
    ∃ n : Fin 16, nativeTranslation n = g := by
  rw [pCoreIn, seed_core_eq_kernel] at hg
  obtain ⟨u, hu, rfl⟩ := hg
  obtain ⟨v, hv⟩ := LinearFourCore.kernelEquiv.surjective ⟨u, hu⟩
  obtain ⟨w, rfl⟩ := heptadBinaryEquiv.surjective v
  obtain ⟨n, hn⟩ := translationVector_surjective w.toAdd
  refine ⟨n, ?_⟩
  unfold nativeTranslation
  rw [hn]
  exact congrArg (fun k : (LinearFourCore.action LinearFourCore.seedOctad).ker =>
    (k.val : M24)) hv

/-- Translation matrices in the star coordinates, with the original relabeling. -/
def translationStar (n : Fin 16) : Equiv.Perm (Fin 24) :=
  MulAut.conj StarOrderCertificate.relabel.symm (nativePerm n)

theorem nativeTranslation_zero : nativeTranslation 0 = 1 := by
  apply Subtype.ext
  rw [nativeTranslation_coe]
  exact (by decide +kernel : nativePerm 0 = 1)

theorem translationStar_eq (n : Fin 16) :
    translationStar n = MulAut.conj StarOrderCertificate.relabel.symm
      (nativeTranslation n : Equiv.Perm (Fin 24)) := by
  rw [nativeTranslation_coe]
  rfl
private def translationColumns : Fin 16 → Fin 11 → ℕ :=
  ![![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024],
    ![2045, 1704, 949, 429, 1722, 1133, 596, 293, 165, 1819, 1020],
    ![164, 266, 41, 8, 280, 168, 456, 128, 256, 640, 1280],
    ![1789, 1952, 573, 429, 1970, 1253, 633, 293, 165, 1598, 857],
    ![1058, 1722, 120, 45, 1704, 1151, 766, 165, 293, 1571, 708],
    ![313, 16, 302, 392, 2, 50, 525, 256, 128, 479, 2015],
    ![1186, 1970, 112, 45, 1952, 1271, 851, 165, 293, 1670, 993],
    ![28, 280, 131, 392, 266, 186, 517, 256, 128, 223, 1887],
    ![180, 266, 43, 256, 280, 186, 1640, 392, 8, 1064, 954],
    ![71, 1952, 1173, 165, 1970, 1271, 883, 45, 429, 1596, 841],
    ![281, 2, 270, 256, 16, 50, 1768, 392, 8, 1440, 946],
    ![79, 1704, 1045, 165, 1722, 1151, 598, 45, 429, 1553, 740],
    ![522, 1970, 1738, 293, 1952, 1253, 587, 429, 45, 1686, 995],
    ![30, 280, 147, 128, 266, 168, 1463, 8, 392, 1637, 503],
    ![898, 1722, 1994, 293, 1704, 1133, 750, 429, 45, 1851, 974],
    ![51, 16, 54, 128, 2, 32, 1207, 8, 392, 1645, 127]]

private theorem translationColumns_eq : ∀ n : Fin 16,
    starMasks (translationStar n) = translationColumns n := by
  decide +kernel

private theorem individual_count : ∀ (n : Fin 16), n ≠ 0 →
    (Finset.univ.filter (fun m : Fin 2048 =>
      maskImage (starMasks (translationStar n)) m.val = m.val)).card = 128 := by
  simp_rw [translationColumns_eq]
  decide +kernel

private theorem pair_count :
    (Finset.univ.filter (fun m : Fin 2048 =>
      maskImage (starMasks (translationStar 1)) m.val = m.val ∧
      maskImage (starMasks (translationStar 2)) m.val = m.val)).card = 64 := by
  simp_rw [translationColumns_eq]
  decide +kernel

theorem translation_fixed_card (n : Fin 16) (hn : n ≠ 0) :
    Nat.card {m : Fin 2048 //
      maskImage (starMasks (translationStar n)) m.val = m.val} = 128 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact individual_count n hn

theorem translation_pair_fixed_card :
    Nat.card {m : Fin 2048 //
      maskImage (starMasks (translationStar 1)) m.val = m.val ∧
      maskImage (starMasks (translationStar 2)) m.val = m.val} = 64 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact pair_count

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.LiteralBinary

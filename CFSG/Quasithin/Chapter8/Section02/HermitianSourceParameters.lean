module

public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianCoordinates
public import CFSG.Quasithin.Chapter8.Section02.Offenders.FixedPoints

/-!
# Hermitian offender parameters on the original ambient subgroup

An equivariant embedding of the actual automizer in the Hermitian normalizer
transports elementary actors, their ranks and their fixed codimensions.
Consequently the source dimension and two-rank premises of the existing
8.2.4 rank-saturation argument follow from the marked action.

The remaining inputs are exactly the earlier global bounds r >= 4n and
w = n, the canonical offender kernel, and H.4.4(3)'s large-actor calculation
on the literal tensor normalizer. No n > 1 exclusion or field-four
centralizer conclusion is assumed or asserted. Their construction and final
assembly belong to qt-d-1222-nonmathieu-hermitian-exclusion. The Chapter 12
application constructs the embedding from the original chosen-module action.

Source: Aschbacher–Smith 8.2.2(7), 8.2.3 and the opening rank calculation
of 8.2.4, printed pp.714–716; H.4.4(3), printed p.381 (refs/quasithin.pdf).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE
variable {G : Type*} [Group G] [Finite G]
  (V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G)
  (n : ℕ) [NeZero n]

/-- H.4.4(3) transfers through the literal automizer embedding, discharging
the dimension and rank bounds in the source offender calculation. -/
theorem offender_parameters_of_coordinates
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
      3 * n ≤ rank A → 5 * n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
    (g : G) (hT : HypothesisE322 V T) (hOff : IsWOffenderAt V T g)
    (hw : globalW V T = n) (hr : ((4 * n : ℕ) : ℕ∞) ≤ globalR V)
    (hkernel : offenderNormalizer V g ⊓ centralizer (V : Set G) =
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    rank (inducedAutomizer V (offenderNormalizer V g)) = 4 * n ∧
      rank (V ⊓ centralizer (offenderNormalizer V g : Set G)) = 4 * n ∧
      V ⊓ centralizer (offenderNormalizer V g : Set G) =
        V ⊓ V.map (MulAut.conj g).toMonoidHom ∧
      globalR V ≤ ((5 * n : ℕ) : ℕ∞) := by
  have hm : primeRank 2 (Automizer V) ≤ 4 * n :=
    (primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n)
        ⟨FieldSections.centralizerEquiv n⟩)
  have hdim : rank V = 9 * n := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    change Nat.card V = _ at hc
    rw [Nat.card_zmod, e.finrank_eq, finrank_binary] at hc
    rw [rank, hc, Nat.log_pow (by decide)]
  apply Offenders.hermitian_offender_parameters V T g n (NeZero.pos n)
    hT hOff hw hr hm hdim hkernel
  intro A hA hrank
  let : IsElementaryAbelian 2 A := hA.2
  have hAj : IsElementaryTwo (A.map j) :=
    ⟨fun hz => hA.1 ((map_eq_bot_iff_of_injective A hj).mp hz),
      IsElementaryAbelian.map j⟩
  have hd := hgeometry (A.map j) hAj (by rwa [rank_map_injective j hj])
  rwa [← fixedCodim_map_equivariant (automizerRepresentation V)
    (overgroupAction n (binaryNormalizer n)) j e he A] at hd

end CFSG.Quasithin.Chapter8.Section02.HermitianSource

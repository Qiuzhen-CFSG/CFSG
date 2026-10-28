module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Construction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Centralizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Recognition
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.IntersectionNormalizer
public import Theory.GroupTheory.PRadical.NormalizerRestriction

/-!
# The native linear-five elementary branch

The linear-five producer supplies a literal elementary subgroup `F` in the
actual J₄ matrix model, together with its exact order and full ambient
centralizer. This leaf records the corresponding two-local and radical
consumer interfaces in the elementary-normalizer development. Every map is
the actual ambient subtype map; no abstract semidirect-product carrier or
unproved normalizer catalogue is introduced here.

The full ambient normalizer and the checked pair of native Q-conjugates are
exported here with their intrinsic 2-core and exterior-action quotient. The
stronger catalogue of every global conjugate lying in the setwise octad
stabilizer remains an explicit premise of the eventual cover theorem.
Source: Kleidman--Wilson, *The Maximal Subgroups of J₄* (1988), pp.490--491.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover

open LinearFive
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

abbrev nativeF : Subgroup Model := LinearFive.F

theorem nativeF_card : Nat.card nativeF = 1024 := LinearFive.F_card

theorem nativeF_elementary : IsElementaryAbelian 2 nativeF :=
  LinearFive.F_elementary

theorem nativeF_nontrivial : nativeF ≠ ⊥ := by
  intro h
  have hc := nativeF_card
  rw [h, card_bot] at hc
  omega

theorem nativeF_le_octad_pullback : nativeF ≤ LinearFive.Q :=
  LinearFive.F_le_Q

theorem nativeF_centralizer : centralizer (nativeF : Set Model) = nativeF :=
  LinearFive.centralizer_F

/- The producer's full ambient normalizer is the concrete generated native
normalizer.  Keeping this equality in the cover namespace lets downstream
branches use the same literal subgroup when transporting local denominators. -/
theorem nativeF_fullNormalizer_eq :
    normalizer (nativeF : Set Model) = LinearFive.M_F := by
  rw [LinearFive.M_F_eq_fullNormalizer]

theorem nativeF_fullNormalizer_twoCore :
    pCore 2 (normalizer (nativeF : Set Model)) = nativeF.subgroupOf
      (normalizer (nativeF : Set Model)) := by
  rw [nativeF_fullNormalizer_eq]
  simpa only [LinearFive.F_M, nativeF] using LinearFive.M_F_twoCore

def nativeF_intrinsic_quotient :
    (normalizer (nativeF : Set Model) ⧸ pCore 2 (normalizer (nativeF : Set Model))) ≃*
      Representation.SL5TenDimensional.Group := by
  rw [nativeF_fullNormalizer_eq]
  exact LinearFive.M_F_intrinsicQuotient

theorem nativeF_exterior_action (n : LinearFive.M_F) (x : LinearFive.F) :
    (LinearFive.exteriorMarking (LinearFive.F.normalizerMonoidHom
      ((MulEquiv.subgroupCongr LinearFive.M_F_eq_fullNormalizer) n) x)).toAdd =
      Representation.SL5TenDimensional.exteriorAction 2
        (LinearFive.pi_F n) (LinearFive.exteriorMarking x).toAdd :=
  LinearFive.pi_F_exterior n x

/- The checked native pair supplies the literal two-occurrence witnesses and
the intersection normalizer bound used by the F branch. -/
theorem nativeF_pair_geometry :
    nativeF ≤ LinearFive.D ∧
      LinearFive.Geometry.secondF ≤ LinearFive.D ∧
      nativeF ≠ LinearFive.Geometry.secondF ∧
      Nat.card (nativeF ⊓ LinearFive.Geometry.secondF : Subgroup Model) = 64 ∧
      nativeF ⊓ LinearFive.Geometry.secondF ≤ LinearFive.E ∧
      centralizer (LinearFive.Geometry.secondF : Set Model) =
        LinearFive.Geometry.secondF ∧
      normalizer (nativeF ⊓ LinearFive.Geometry.secondF : Set Model) ≤ LinearFive.M :=
  LinearFive.Geometry.native_pair_geometry

theorem nativeF_E_conjugate (z : Model) (hz : z ∈ LinearFive.E) :
    nativeF.map (MulAut.conj z).toMonoidHom = nativeF ∨
      nativeF.map (MulAut.conj z).toMonoidHom = LinearFive.Geometry.secondF :=
  LinearFive.Geometry.E_conjugates z hz

theorem nativeF_Q_conjugate (q : Model) (hq : q ∈ LinearFive.Q) :
    nativeF.map (MulAut.conj q).toMonoidHom = nativeF ∨
      nativeF.map (MulAut.conj q).toMonoidHom = LinearFive.Geometry.secondF :=
  LinearFive.Geometry.Q_conjugates q hq

theorem nativeF_E_conjugates_exact :
    {H : Subgroup Model | ∃ z : Model, z ∈ LinearFive.E ∧
      nativeF.map (MulAut.conj z).toMonoidHom = H} =
      {nativeF, LinearFive.Geometry.secondF} :=
  LinearFive.Geometry.E_conjugates_exact

theorem nativeF_normalizer_not_le_max1 :
    ¬ normalizer (nativeF : Set Model) ≤ LinearFive.M := by
  intro h
  apply LinearFive.fullNormalizer_not_le_M
  rw [← LinearFive.M_F_eq_fullNormalizer]
  rw [← nativeF_fullNormalizer_eq]
  exact h

/-- The full normalizer of the native `F` is a genuine two-local, witnessed by
`F` itself. This does not identify that normalizer with any guessed
matrix-word subgroup. -/
theorem nativeF_normalizer_isTwoLocal :
    IsTwoLocal (normalizer (nativeF : Set Model)) :=
  ⟨nativeF, nativeF_nontrivial, nativeF_elementary.isPGroup 2, rfl⟩

theorem nativeF_generated_isTwoLocal : IsTwoLocal LinearFive.M_F := by
  rw [← nativeF_fullNormalizer_eq]
  exact nativeF_normalizer_isTwoLocal

theorem nativeF_intersection_embeddedKernel_card :
    Nat.card (nativeF ⊓ LinearFive.E : Subgroup Model) = 64 :=
  LinearFive.F_inf_E_card

/-- Literal local restriction for a radical whose whole ambient normalizer is
known to normalize the native `F`. The theorem keeps the required source
premise explicit while discharging all denominator and core identities. -/
theorem radical_local_of_nativeF_normalizer
    (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hNP : normalizer (P : Set Model) ≤ normalizer (nativeF : Set Model)) :
    let M := normalizer (nativeF : Set Model)
    IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  dsimp only
  let M : Subgroup Model := normalizer (nativeF : Set Model)
  have hPM : P ≤ M := P.le_normalizer.trans hNP
  have hNN : normalizer (P : Set Model) ≤ normalizer (M : Set Model) :=
    hNP.trans M.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf M hPM hNN
  refine ⟨nativeF_normalizer_isTwoLocal, hNP, hPM, ?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hNN, hcore, ?_⟩
  · rw [← subgroupOf_normalizer_eq hPM, map_subgroupOf_eq_of_le hNP]
  · rw [hcore, map_subgroupOf_eq_of_le hPM]

/- The same radical consumer with the concrete generated normalizer as its
public local carrier.  This is the interface used by the parent quotient rows. -/
theorem radical_local_of_nativeF_generated
    (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hNP : normalizer (P : Set Model) ≤ LinearFive.M_F) :
    IsTwoLocal LinearFive.M_F ∧
      normalizer (P : Set Model) ≤ LinearFive.M_F ∧ P ≤ LinearFive.M_F ∧
      (normalizer (P.subgroupOf LinearFive.M_F : Set LinearFive.M_F)).map
          LinearFive.M_F.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf LinearFive.M_F).IsPRadical 2 ∧
      (normalizer (P.subgroupOf LinearFive.M_F : Set LinearFive.M_F)).pCoreIn 2 =
        P.subgroupOf LinearFive.M_F ∧
      ((normalizer (P.subgroupOf LinearFive.M_F : Set LinearFive.M_F)).pCoreIn 2).map
          LinearFive.M_F.subtype = P := by
  have hPM : P ≤ LinearFive.M_F := P.le_normalizer.trans hNP
  have hNN : normalizer (P : Set Model) ≤ normalizer (LinearFive.M_F : Set Model) :=
    hNP.trans LinearFive.M_F.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf LinearFive.M_F hPM hNN
  refine ⟨?_, hNP, hPM, ?_,
    hP.subgroupOf_of_normalizer_normalizes LinearFive.M_F hPM hNN, hcore, ?_⟩
  · rw [← nativeF_fullNormalizer_eq]
    exact nativeF_normalizer_isTwoLocal
  · rw [← subgroupOf_normalizer_eq hPM, map_subgroupOf_eq_of_le hNP]
  · rw [hcore, map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.ElementaryNormalizerCover

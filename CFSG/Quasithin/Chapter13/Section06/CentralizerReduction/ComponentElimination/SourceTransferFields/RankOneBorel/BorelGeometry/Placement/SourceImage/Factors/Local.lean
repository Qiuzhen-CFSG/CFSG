module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.AlternatingObstruction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Factors.ModelSeeds
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Applying factor selection to the actual local actor

The image of O²(KT_v) is the marked K⁺. Its natural-section actor identifies
this actual residual with SL₂(F), and the block has |F|≥4. Thus the residual
is simple. Apply the factor-selection theorem to the image of global J(KT_v)
and its genuine E.2.3 decomposition to obtain a single factor.

The local source application uses the existing characteristic-two,
centralizer-kernel and Thompson-noncentrality proofs. Only the independent
minimal-parabolic, SQTK and reducedness inputs and the universal E.2.3 source
implication remain explicit. There is no assumption L_v≤K or Borel placement.
This module selects the factor; distinguishing its module alternatives and
identifying the whole Thompson image with its residual remain separate steps.

Source: Aschbacher–Smith E.2.3(1) and 13.6.18, printed pp.216–217 and 931.
-/

@[expose] public section
open Subgroup Stellmacher Matrix
open scoped MatrixGroups IsMulCommutative
open Matrix.SpecialLinearGroup.RankOneResidual
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceFactors
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
variable (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
  (movingSpace K L T z v))

/-- An actual isomorphism from the local range's residual to the given SL₂
model, through its literal ambient range image and the marked K⁺. -/
noncomputable def localResidualEquiv :
    pResidual 2 (localMap K L T z v hL hz).range ≃* SL(2,F) :=
  (((pResidual 2 (localMap K L T z v hL hz).range).equivMapOfInjective
    (localMap K L T z v hL hz).range.subtype
    (localMap K L T z v hL hz).range.subtype_injective).trans
      (MulEquiv.subgroupCongr (localRange_residual_image K L T z v hL hz hK hnorm hb))).trans
        s.actor

include hK hnorm hF hb s

omit [Finite F] in
/-- The intrinsic residual is simple. The source block excludes the exceptional
prime-field group; no simplicity premise is added to the local application. -/
theorem localResidual_simple :
    IsSimpleGroup (pResidual 2 (localMap K L T z v hL hz).range) := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    change 2 ^ 2 ≤ 2 ^ n
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by have := hb.1; omega)
  let : IsSimpleGroup PSL(2,F) := ProjectiveSpecialLinearGroup.rank_two_simple hfour
  exact ((localResidualEquiv K L T z v hL hz hK hnorm hb s).trans
    Atlas.RankOneFieldAutomorphisms.slEquivPSL).isSimpleGroup

omit [Finite F] in
/-- The actual E.2.3 decomposition of J(KT_v)* has one factor. This conclusion
uses the model isomorphisms to supply the odd-order elements in both branches. -/
theorem localDecomposition_size_eq_one
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (d : Decomposition (localProjection K L T z v hL hz)
      ((Tv T v).subgroupOf (K ⊔ Tv T v))
      (localRepresentation K L T z v hL hz hW)) :
    d.factors.size = 1 := by
  let := localResidual_simple K L T z v hL hz hK hnorm hF hb s
  exact d.size_eq_one (localMap K L T z v hL hz).rangeRestrict_surjective

omit [Finite F] in
/-- The selected factor is the actual global Thompson image inside the local
range; it is not the Thompson subgroup of the range. -/
theorem local_selectedFactor_eq_globalImage
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (d : Decomposition (localProjection K L T z v hL hz)
      ((Tv T v).subgroupOf (K ⊔ Tv T v))
      (localRepresentation K L T z v hL hz hW)) (i : Fin d.factors.size) :
    (d.factors.factor i).map (globalImage (localProjection K L T z v hL hz)).subtype =
      globalImage (localProjection K L T z v hL hz) := by
  rw [unique_factor_top d.factors
    (localDecomposition_size_eq_one K L T z v hL hz hK hnorm hF hb s hW d) i,
    ← MonoidHom.range_eq_map, range_subtype]

/-- The faithful local source hypotheses instantiate the universal E.2.3
implication. Reducedness and minimal-parabolic status are independent inputs;
the source implication belongs to the Chapter E theorem owner. -/
theorem local_source_decomposition
    {𝒞 : GroupClass} (hE23 : SourceImplication 𝒞)
    (hq : IsSQTK 𝒞 (Gv v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction (Tv T v) K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (P : Sylow 2 (K ⊔ Tv T v : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv T v : Subgroup G)) =
      (Tv T v).subgroupOf (K ⊔ Tv T v))
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (hred : pCore 2 (localMap K L T z v hL hz).range = ⊥) :
    Nonempty (Decomposition (localProjection K L T z v hL hz)
      ((Tv T v).subgroupOf (K ⊔ Tv T v))
      (localRepresentation K L T z v hL hz
        ((WK_le_Tv K L T z v hK.1.1 hSylow hzOmega hf).trans le_sup_right))) := by
  have hW := (WK_le_Tv K L T z v hK.1.1 hSylow hzOmega hf).trans
    (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)
  have hnc : ¬ elementaryAbelianMaxJ (P : Subgroup (K ⊔ Tv T v : Subgroup G)) ≤
      centralizer (internalWK K L T z v hL hz : Set (K ⊔ Tv T v : Subgroup G)) := by
    rw [hP, local_thompson_subgroupOf, ← localMap_ker_internal K L T z v hL hz hW,
      localMap_ker]
    intro hc
    apply local_thompson_noncentral K L T z v hL hz hK hnorm hF hb s hzOmega hpush
    intro x hx
    have hxH : x ∈ K ⊔ Tv T v :=
      (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)
        ((show elementaryAbelianMaxJ (Tv T v) ≤ Tv T v from
          sSup_le fun _ hA => hA.1) hx)
    exact hc (show (⟨x, hxH⟩ : (K ⊔ Tv T v : Subgroup G)) ∈
      (elementaryAbelianMaxJ (Tv T v)).subgroupOf (K ⊔ Tv T v) from hx)
  have hd := hE23 P (internalWK K L T z v hL hz)
    (localProjection K L T z v hL hz) (localMap K L T z v hL hz).rangeRestrict_surjective
    (localProjection_ker K L T z v hL hz hW)
    (local_sqtk K T v hK.1.1 hq) hmin
    (local_fitting_eq K T v hK.1.1 hSylow hf) hred hnc
  simpa only [hP, localRepresentation] using hd

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceFactors
end

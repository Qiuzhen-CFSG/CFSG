module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.AlternatingObstruction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Factors.Local
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Factors.AlternatingTransfer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Factors.LinearResidual

/-!
# The global Thompson image is the marked rank-one factor

The source input retains the actual image of global J(H), its internal direct
product, equivariant factor models and fixed-space quotients. The simple
residual SL₂(F), with |F|≥4, forces exactly one factor. The symmetric alternative
would embed the A₅ permutation module equivariantly into the literal moving
section, contradicting its natural SL₂ action even when |F|=4. The remaining
linear factor is perfect; the exceptional field of order two is excluded by
the nontrivial perfect residual. Thus J(H)*=O²(H)*=K⁺.

The universal E.2.3 group/module implication is explicitly instantiated on
H=KT_v and its centralizer quotient, using the earlier local preparation.
Minimal-parabolic status, reducedness and the independent SQTK input remain
explicit. The universal source theorem remains with the Chapter E owner.

The final source applications discharge all factor-comparison premises.
No Borel-placement or L_v≤K hypothesis is used. The parent SourceImage owner
retains the subsequent Baumann-image containment assembly.

Source: Aschbacher–Smith E.2.3, printed pp.216–217; B.6.9, pp.115–116;
13.6.18, p.931 (combined manuscript of 1 March 2004).
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

section Decomposition
variable (hW : WK K L T z v ≤ K ⊔ Tv T v)
variable (d : Decomposition (localProjection K L T z v hL hz)
  ((Tv T v).subgroupOf (K ⊔ Tv T v))
  (localRepresentation K L T z v hL hz hW))

include hK hnorm hb s in
omit [Finite F] in
/-- Every factor has genuine linear coordinates. The symmetric alternative
is excluded using its actual action, without assuming the image equality. -/
theorem localDecomposition_linearFactor (i : Fin d.factors.size) :
    Nonempty (LinearFactor
      ((localRepresentation K L T z v hL hz hW).comp
        (globalImage (localProjection K L T z v hL hz)).subtype)
      ((pResidual 2 (localMap K L T z v hL hz).range).subgroupOf
        (globalImage (localProjection K L T z v hL hz))) (d.factors.factor i)) := by
  cases d.modules i with
  | linear m => exact ⟨m⟩
  | symmetric m =>
    exact (localDecomposition_not_symmetricFactor K L T z v hL hz hK hnorm hb s hW d i m).elim

include hK hnorm hF hb s hW d

/-- The actual image of global J(KT_v) is the local range's two-residual.
Singleton selection and both model alternatives are discharged here. -/
theorem localDecomposition_globalImage_eq_residual :
    globalImage (localProjection K L T z v hL hz) =
      pResidual 2 (localMap K L T z v hL hz).range := by
  let i := localSelectedIndex K L T z v hL hz hK hnorm hF hb s hW d
  obtain ⟨m⟩ := localDecomposition_linearFactor K L T z v hL hz hK hnorm hb s hW d i
  exact local_linear_globalImage_eq_residual K L T z v hL hz hK hnorm hF hb s hW d i m

/-- In the literal plus quotient the image of global J(KT_v) is K⁺.
This is the image of the original Thompson subgroup, not J of the quotient. -/
theorem localDecomposition_thompson_image :
    (elementaryAbelianMaxJ (⊤ : Subgroup (K ⊔ Tv T v : Subgroup G))).map
      (localMap K L T z v hL hz) = plusImage K L T z v hL hz K := by
  have he := congrArg (fun U : Subgroup (localMap K L T z v hL hz).range =>
    U.map (localMap K L T z v hL hz).range.subtype)
    (localDecomposition_globalImage_eq_residual K L T z v hL hz hK hnorm hF hb s hW d)
  rw [localRange_residual_image K L T z v hL hz hK hnorm hb, globalImage, Subgroup.map_map] at he
  exact he

/-- The same image equality with global J(KT_v) written as a subgroup of G,
then restricted to the actual domain of the local quotient map. -/
theorem localDecomposition_ambient_thompson_image :
    ((elementaryAbelianMaxJ (K ⊔ Tv T v)).subgroupOf (K ⊔ Tv T v)).map
      (localMap K L T z v hL hz) = plusImage K L T z v hL hz K := by
  let i := localSelectedIndex K L T z v hL hz hK hnorm hF hb s hW d
  obtain ⟨m⟩ := localDecomposition_linearFactor K L T z v hL hz hK hnorm hb s hW d i
  exact local_linear_ambient_thompson_image K L T z v hL hz hK hnorm hF hb s hW d i m

end Decomposition

section Source
variable {𝒞 : GroupClass} (hE23 : SourceImplication 𝒞)
variable (hq : IsSQTK 𝒞 (Gv v))
variable (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
variable (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction (Tv T v) K)
variable (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
variable (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
variable (P : Sylow 2 (K ⊔ Tv T v : Subgroup G))
variable (hP : (P : Subgroup (K ⊔ Tv T v : Subgroup G)) =
  (Tv T v).subgroupOf (K ⊔ Tv T v))
variable (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
variable (hred : pCore 2 (localMap K L T z v hL hz).range = ⊥)

include hK hnorm hF hb s hE23 hq hzOmega hpush hSylow hf P hP hmin hred

/-- Actual local application of the source decomposition: the global
Thompson image is the residual, with no selected-factor premise remaining. -/
theorem local_source_globalImage_eq_residual :
    globalImage (localProjection K L T z v hL hz) =
      pResidual 2 (localMap K L T z v hL hz).range := by
  obtain ⟨d⟩ := local_source_decomposition K L T z v hL hz hK hnorm hF hb s
    hE23 hq hzOmega hpush hSylow hf P hP hmin hred
  exact localDecomposition_globalImage_eq_residual K L T z v hL hz hK hnorm hF hb s
    ((WK_le_Tv K L T z v hK.1.1 hSylow hzOmega hf).trans le_sup_right) d

/-- The source hypotheses give J(KT_v)*=K⁺ under the literal local map.
The universal E.2.3 implication and independent earlier source inputs remain
explicit; all factor-comparison premises have been discharged. -/
theorem local_source_thompson_image :
    (elementaryAbelianMaxJ (⊤ : Subgroup (K ⊔ Tv T v : Subgroup G))).map
      (localMap K L T z v hL hz) = plusImage K L T z v hL hz K := by
  obtain ⟨d⟩ := local_source_decomposition K L T z v hL hz hK hnorm hF hb s
    hE23 hq hzOmega hpush hSylow hf P hP hmin hred
  exact localDecomposition_thompson_image K L T z v hL hz hK hnorm hF hb s
    ((WK_le_Tv K L T z v hK.1.1 hSylow hzOmega hf).trans le_sup_right) d

/-- The ambient-subgroup form for the parent Baumann-image assembly.
In particular no L_v≤K or Borel-placement assumption is used. -/
theorem local_source_ambient_thompson_image :
    ((elementaryAbelianMaxJ (K ⊔ Tv T v)).subgroupOf (K ⊔ Tv T v)).map
      (localMap K L T z v hL hz) = plusImage K L T z v hL hz K := by
  obtain ⟨d⟩ := local_source_decomposition K L T z v hL hz hK hnorm hF hb s
    hE23 hq hzOmega hpush hSylow hf P hP hmin hred
  exact localDecomposition_ambient_thompson_image K L T z v hL hz hK hnorm hF hb s
    ((WK_le_Tv K L T z v hK.1.1 hSylow hzOmega hf).trans le_sup_right) d

end Source
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceFactors
end

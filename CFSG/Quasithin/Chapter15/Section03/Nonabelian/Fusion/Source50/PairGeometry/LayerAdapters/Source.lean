module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters.Finite

/-!
# The canonical source (54) layer actions at multiplicity one

The source module witness retains the intrinsic I/O₂(I) coordinates.
Central collapse changes its section kernel to V without changing its
representation or multiplicity. We combine the same witness with the
specified determinant action on V, and specialize its ordered natural
summands at s = 1. Both compatibility equations use literal conjugation.

The cardinality formula also retains this same multiplicity. The lower
coordinate change preserves the original determinant marking.

Source: Aschbacher–Smith, G.2.6 and 15.3.54, 15.3.58(2), 15.3.59,
printed pp.336, 1146, 1148, and 1150.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters
open scoped IsMulCommutative
open Subgroup Core.Automizers Core.Automizers.Models
open ClassicalOrthogonal.FourPlusMatrix
open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour
open OrthogonalPlusFour.Chapter15Assembly OrthogonalPlusFour.Chapter15Collapse
open OrthogonalPlusFour.Multiplicity
open Representation.BinaryQuadraticPair InvertedCubicTensor
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

def matrixActor (d : OrthogonalPlusFour.Hypothesis D g) : D.I g →* Actor :=
  d.quotientMatrixEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g)))

theorem matrixActor_onto (d : OrthogonalPlusFour.Hypothesis D g) : Function.Surjective (matrixActor d) :=
  d.quotientMatrixEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

theorem matrixActor_ker (d : OrthogonalPlusFour.Hypothesis D g) :
    (matrixActor d).ker = (D.S g).subgroupOf (D.I g) := by
  rw [matrixActor, MonoidHom.ker_comp_of_injective _ _ d.quotientMatrixEquiv.injective,
    QuotientGroup.ker_mk']
  change pCore 2 (D.I g) = ((pCore 2 (D.I g)).map (D.I g).subtype).comap (D.I g).subtype
  exact (comap_map_eq_self_of_injective (D.I g).subtype_injective _).symm

theorem matrixActor_image_L (d : OrthogonalPlusFour.Hypothesis D g) :
    (D.L.subgroupOf (D.I g)).map (matrixActor d) = nine := by
  have he : matrixActor d = OrthogonalPlusFour.Hypothesis.pairPermEquiv.symm.toMonoidHom.comp
      (d.quotientSymmetricEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g)))) := by
    apply MonoidHom.ext
    intro i
    change d.quotientMatrixEquiv (QuotientGroup.mk' _ i) =
      OrthogonalPlusFour.Hypothesis.pairPermEquiv.symm (d.quotientSymmetricEquiv (QuotientGroup.mk' _ i))
    rw [d.quotientMatrixEquiv_mk, d.quotientSymmetricEquiv_mk,
      MulEquiv.symm_apply_apply]
  rw [he, ← map_map, d.quotientSymmetricEquiv_L_image]
  exact map_alternating_pair_eq_nine (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)

theorem lower_coordinates_compatible (d : OrthogonalPlusFour.Hypothesis D g) (i : D.I g) (v : D.VL) :
    (d.coordinates.trans determinantToTensor) (lowerAction (D.I g) D.VL d.I_normalizes_VL i v) =
      tensorAction (matrixActor d i) ((d.coordinates.trans determinantToTensor) v) := by
  have he := d.quotientMatrixEquiv_equivariant i v
  have hf : d.coordinates (lowerAction (D.I g) D.VL d.I_normalizes_VL i v) =
      Multiplicative.ofAdd (matrixAction (matrixActor d i) (d.coordinates v).toAdd) := by
    apply d.coordinates.symm.injective
    apply Subtype.ext
    rw [d.coordinates.symm_apply_apply]
    exact he.symm
  change determinantToTensor (d.coordinates _) = _
  rw [hf]
  exact determinantToTensor_compatible _ _

variable [((OrthogonalPlusFour.S₂ D g).subgroupOf (D.S g)).Normal]
  [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient D g)]

def canonicalFactorData (d : OrthogonalPlusFour.Hypothesis D g) (f : SourceModuleData d)
    (hΩ : omegaCenter D.T ≤ D.VL) :
    FactorData (D.I g) (D.S g) D.VL D.L (Additive (OrthogonalPlusFour.Quotient D g)) :=
  factorData_of_source f hΩ

theorem canonicalFactorData_model (d : OrthogonalPlusFour.Hypothesis D g) (f : SourceModuleData d)
    (hΩ : omegaCenter D.T ≤ D.VL) :
    (canonicalFactorData d f hΩ).model = d.quotientSymmetricEquiv := rfl

theorem canonicalFactorData_common (d : OrthogonalPlusFour.Hypothesis D g) (f : SourceModuleData d)
    (hΩ : omegaCenter D.T ≤ D.VL) (hexchange : FactorExchange d) :
    (canonicalFactorData d f hΩ).decomposition.leftMultiplicity =
      (canonicalFactorData d f hΩ).decomposition.rightMultiplicity :=
  f.common_of_factorExchange hexchange

theorem canonicalFactorData_core_card (d : OrthogonalPlusFour.Hypothesis D g)
    (f : SourceModuleData d) (hΩ : omegaCenter D.T ≤ D.VL)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity) :
    Nat.card (D.S g) = 2 ^ (4 * f.decomposition.leftMultiplicity + 4) := by
  have hcore : Nat.card ThreeCore = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), BinaryPermutation.finrank_core]
    norm_num [Nat.card_eq_fintype_card]
  have hV : Nat.card D.VL = 2 ^ 4 := by
    rw [Nat.card_congr d.coordinates.toEquiv]
    change Nat.card (Fin 2 → Fin 2 → ZMod 2) = 2 ^ 4
    simp
  have hM : Nat.card (Additive (OrthogonalPlusFour.Quotient D g)) =
      2 ^ (4 * f.decomposition.leftMultiplicity) := by
    rw [Nat.card_congr (commonSumEquiv f.decomposition hsame).symm.toEquiv,
      Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, hcore]
    change ((2 ^ 2) ^ f.decomposition.leftMultiplicity) ^ 2 = _
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [(canonicalFactorData d f hΩ).conjugation.card_section, hM, hV, ← pow_add]

def upperCoordinatesOfOne (d : OrthogonalPlusFour.Hypothesis D g) (f : SourceModuleData d)
    (hΩ : omegaCenter D.T ≤ D.VL)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity)
    (hone : f.decomposition.leftMultiplicity = 1)
    [(D.VL.subgroupOf (D.S g)).Normal] :
    (D.S g ⧸ D.VL.subgroupOf (D.S g)) ≃* SumVector :=
  (commonQuotientEquiv (σ := f.representation) (canonicalFactorData d f hΩ).conjugation f.decomposition hsame).trans
    (multiplicityOneCoordinates hone (Classical.choose (exists_coreCoordinates
      (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))))

theorem upperCoordinatesOfOne_compatible (d : OrthogonalPlusFour.Hypothesis D g) (f : SourceModuleData d)
    (hΩ : omegaCenter D.T ≤ D.VL)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity)
    (hone : f.decomposition.leftMultiplicity = 1)
    [(D.VL.subgroupOf (D.S g)).Normal] (i : D.I g)
    (v : D.S g ⧸ D.VL.subgroupOf (D.S g)) :
    upperCoordinatesOfOne d f hΩ hsame hone
      (upperAction (D.I g) (D.S g) D.VL
        (canonicalFactorData d f hΩ).conjugation.normalized d.I_normalizes_VL i v) =
      sumAction (matrixActor d i) (upperCoordinatesOfOne d f hΩ hsame hone v) := by
  induction v using QuotientGroup.induction_on with
  | H p =>
    change upperCoordinatesOfOne d f hΩ hsame hone
      (upperAction (D.I g) (D.S g) D.VL
        (canonicalFactorData d f hΩ).conjugation.normalized d.I_normalizes_VL i
        (QuotientGroup.mk' (D.VL.subgroupOf (D.S g)) p)) = _
    rw [upperAction_mk]
    let c := Classical.choose (exists_coreCoordinates
      (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))
    have hc := Classical.choose_spec (exists_coreCoordinates
      (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))
    have he := commonQuotientEquiv_conjugation (σ := f.representation)
      (canonicalFactorData d f hΩ).conjugation f.decomposition hsame i p
    have hm : (canonicalFactorData d f hΩ).model (QuotientGroup.mk' _ i) =
        OrthogonalPlusFour.Hypothesis.pairPermEquiv (matrixActor d i) := by
      change d.quotientSymmetricEquiv (QuotientGroup.mk' _ i) =
        OrthogonalPlusFour.Hypothesis.pairPermEquiv (d.quotientMatrixEquiv (QuotientGroup.mk' _ i))
      rw [d.quotientSymmetricEquiv_mk, d.quotientMatrixEquiv_mk]
    have he' : commonQuotientEquiv (σ := f.representation)
        (canonicalFactorData d f hΩ).conjugation f.decomposition hsame
        (QuotientGroup.mk' _ ⟨(i : G) * p * (i : G)⁻¹,
          le_normalizer_iff.mp (canonicalFactorData d f hΩ).conjugation.normalized
            i i.property p p.property⟩) =
        Multiplicative.ofAdd (fun k j => BinaryPermutation.coreRepresentation (Fin 3)
          (if k = 0 then (OrthogonalPlusFour.Hypothesis.pairPermEquiv (matrixActor d i)).1 else
            (OrthogonalPlusFour.Hypothesis.pairPermEquiv (matrixActor d i)).2)
          ((commonQuotientEquiv (σ := f.representation) (canonicalFactorData d f hΩ).conjugation
            f.decomposition hsame (QuotientGroup.mk' _ p)).toAdd k j)) := by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_ofAdd]
      simpa only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hm] using he
    exact (congrArg (multiplicityOneCoordinates hone c) he').trans
      (multiplicityOneCoordinates_compatible hone
        (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three) c hc (matrixActor d i) _)

def layersOfSourceData (d : OrthogonalPlusFour.Hypothesis D g) (f : SourceModuleData d)
    (hΩ : omegaCenter D.T ≤ D.VL)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity)
    (hone : f.decomposition.leftMultiplicity = 1)
    [(D.VL.subgroupOf (D.S g)).Normal] :
    LayerActions (D.I g) D.L (D.S g) D.VL
      (canonicalFactorData d f hΩ).conjugation.normalized d.I_normalizes_VL where
  actor := matrixActor d
  onto := matrixActor_onto d
  kernel := matrixActor_ker d
  image_Y := matrixActor_image_L d
  lowerCoordinates := d.coordinates.trans determinantToTensor
  upperCoordinates := upperCoordinatesOfOne d f hΩ hsame hone
  lower_compatible := lower_coordinates_compatible d
  upper_compatible := upperCoordinatesOfOne_compatible d f hΩ hsame hone

theorem layersOfSourceData_lower (d : OrthogonalPlusFour.Hypothesis D g) (f : SourceModuleData d)
    (hΩ : omegaCenter D.T ≤ D.VL)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity)
    (hone : f.decomposition.leftMultiplicity = 1)
    [(D.VL.subgroupOf (D.S g)).Normal] (v : D.VL) :
    (layersOfSourceData d f hΩ hsame hone).lowerCoordinates v =
      determinantToTensor (d.coordinates v) := rfl

theorem layersOfSourceData_determinant (d : OrthogonalPlusFour.Hypothesis D g)
    (f : SourceModuleData d) (hΩ : omegaCenter D.T ≤ D.VL)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity)
    (hone : f.decomposition.leftMultiplicity = 1)
    [(D.VL.subgroupOf (D.S g)).Normal] (v : D.VL) :
    determinantForm ((layersOfSourceData d f hΩ hsame hone).lowerCoordinates v).toAdd =
      determinantForm (d.coordinates v).toAdd :=
  determinantToTensor_determinant _

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters

module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Constructions
public import Theory.GroupTheory.SylowKernelCore

/-!
# Ambient source geometry for terminal coordinates

The intrinsic pre-intersection input lives in G₀. The earlier ambient
geometry identifies its Sylow subgroup, two residual factors and singular
commutator plane with their literal source constructions. Mapping the
intrinsic relations through the inclusion of G₀ constructs the marked-plane
configuration. In particular its core bound, local quotient, commutator and
Thompson containment are proved from the original input and the non-S₃
intersection, rather than supplied a second time as geometric assumptions.

All geometric inputs below precede hexacode recognition: the compatible
natural orthogonal action, the residual product, the singular-plane choice
and its conjugator, and relative normalization. Their construction in the
proof of Theorem 15.3.1 remains with the earlier local source owners. The
centrality of O₂(G₀), already in the intrinsic input, is not proved here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.3.7 and 15.3.66–68, printed pp.1122 and 1152–1155 (PDF p.1172 for
the final coordinate and definite-plane argument).
-/

@[expose] public section

open Subgroup
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction

open AbelianAmalgam
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

universe u
variable {G : Type u} [Group G] [Finite G] {G₀ M V : Subgroup G}
  (d : NaturalOrthogonalAction M V)
  (a : Intersection.SourceInput (V.subgroupOf G₀))

/-- Earlier ambient geometry, aligned with the intrinsic local input by the
actual subgroup inclusion. No coordinate, scalar or plane-orbit conclusion
occurs here; even the Thompson containment is derived after classification. -/
structure EarlierGeometry where
  T : Sylow 2 G
  Mc : Subgroup G
  E : Subgroup G
  s : G
  sylow_le : (T : Subgroup G) ≤ M
  vector_eq : V = localModule T M
  singular_card : Nat.card E = 4
  singular : MarkedPlane.IsSingularIn M V E d
  sylow_map : (a.T : Subgroup G₀).map G₀.subtype = lineT T E
  first_map : a.YF.map G₀.subtype = otherLine (lineY (residualY M Mc) E) s
  second_map : a.XE.map G₀.subtype = lineX E
  singular_map : a.F.map G₀.subtype = otherLine E s
  conjugator_mem : s ∈ planeStabilizer T (d.plane 1)
  conjugator_not_mem : s ∉ lineT T E
  residual_image : d.image (residualY M Mc) = pResidual 2 OrthogonalActor
  ambient_product : M = residualY M Mc ⊔ (T : Subgroup G)
  residual_product : (residualY M Mc : Set G) =
    (lineY (residualY M Mc) E : Set G) *
      (otherLine (lineY (residualY M Mc) E) s : Set G) *
      ((residualY M Mc).pCoreIn 2 : Set G)
  /-- Relative normalization from 15.3.68(1). -/
  residual_normalized : G₀ ≤ normalizer (lineY (residualY M Mc) E : Set G)
  /-- The kernel bound from 15.3.7. -/
  residual_core_le : (residualY M Mc).pCoreIn 2 ≤ centralizer (V : Set G)
  /-- The ambient centralizer identity of 15.3.67(1). -/
  centralizer_le : centralizer (V : Set G) ≤ lineT T E
  /-- 15.3.66(5), on the original singular plane. -/
  first_commutator : V = ⁅V, lineY (residualY M Mc) E⁆

private theorem intrinsic_twoResidual_eq (P : Subgroup G) :
    Stellmacher.twoResidualSubgroup P = pResidual 2 P := by
  unfold Stellmacher.twoResidualSubgroup pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hN, hn⟩
    exact ⟨hN, IsPGroup.iff_card.mpr (by simpa only [index_eq_card] using hn)⟩
  · rintro ⟨hN, hn⟩
    exact ⟨hN, by simpa only [index_eq_card] using hn.exists_card_eq⟩

namespace EarlierGeometry

variable {d a} (g : EarlierGeometry d a)
include g

omit [Finite G] in
/-- The intrinsic common Sylow maps to the literal `T_E`, hence lies in G₀. -/
theorem sylow_part_le : lineT g.T g.E ≤ G₀ :=
  g.sylow_map ▸ map_subtype_le _

omit [Finite G] in
/-- The original vector group embeds in G₀, using its actual ambient centralizer. -/
theorem vector_le : V ≤ G₀ := by
  let _ := d.elementary
  exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
    (g.centralizer_le.trans g.sylow_part_le)

omit [Finite G] in
/-- Restricting the vector centralizer and mapping back recovers the full
ambient centralizer, because that centralizer lies in the common Sylow. -/
theorem centralizer_map :
    (centralizer (V.subgroupOf G₀ : Set G₀)).map G₀.subtype = centralizer (V : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ v hv
    exact congrArg G₀.subtype (hy ⟨v, g.vector_le hv⟩ hv)
  · intro hx
    refine ⟨⟨x, g.sylow_part_le (g.centralizer_le hx)⟩, ?_, rfl⟩
    intro v hv
    exact Subtype.ext (hx v.val hv)

omit [Finite G] in
/-- The intrinsic R maps to the original ambient centralizer. -/
theorem centralizer_subgroup_map : a.R.map G₀.subtype = centralizer (V : Set G) := by
  rw [a.centralizer_eq, g.centralizer_map]

omit [Finite G] in
/-- The source module has its required elementary abelian structure: the
natural four-space lies in the center of the intrinsic two-core. -/
theorem moduleClosure_elementary : IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀)) := by
  let _ := d.elementary
  let _ := IsElementaryAbelian.subgroupOf (p := 2) g.vector_le
  exact TerminalRecognition.moduleClosure_elementary _ a.vector_le_core a.core_centralizes

/-- Construct every marked-plane input on the same local groups and conjugator.
Only the proved non-S₃ Thompson containment is needed from the intersection. -/
noncomputable def configuration (hYF : a.YF ≤ thompsonGroup G₀) :
    MarkedPlane.SourceConfiguration G₀ M V d := by
  let YE := lineY (residualY M g.Mc) g.E
  let YF := otherLine YE g.s
  have hYFmap : a.YF.map G₀.subtype = YF := g.first_map
  have hVmap : (V.subgroupOf G₀).map G₀.subtype = V :=
    map_subgroupOf_eq_of_le g.vector_le
  have hYF : YF.subgroupOf G₀ ≤ thompsonGroup G₀ := by
    rw [← hYFmap]
    simpa only [← comap_subtype, comap_map_eq_self_of_injective G₀.subtype_injective]
      using hYF
  have hG1 : a.G1.map G₀.subtype = YF ⊔ lineT g.T g.E := by
    rw [a.first_local, Subgroup.map_sup, hYFmap, g.sylow_map]
  have hG2 : a.G2.map G₀.subtype = lineX g.E ⊔ lineT g.T g.E := by
    rw [a.second_local, Subgroup.map_sup, g.second_map, g.sylow_map]
  have hgen : G₀ = a.G1.map G₀.subtype ⊔ a.G2.map G₀.subtype := by
    rw [← Subgroup.map_sup, a.generated, ← MonoidHom.range_eq_map, range_subtype]
  have hnorm : lineT g.T g.E ≤ normalizer (YF : Set G) := by
    rw [← g.sylow_map, ← hYFmap]
    exact (map_mono ((a.first_local.symm ▸ le_sup_right).trans
      a.first_normalized)).trans (le_normalizer_map _)
  have hcore : G₀.pCoreIn 2 ⊔ YF.pCoreIn 2 ≤ centralizer (V : Set G) := by
    have h := map_mono (f := G₀.subtype) a.core_bound
    rw [Subgroup.map_sup, map_pCoreIn_of_injective 2 _ _ G₀.subtype_injective,
      hYFmap, g.centralizer_subgroup_map] at h
    exact h
  have hsecond : V = ⁅V, YF⁆ := by
    have h := congrArg (Subgroup.map G₀.subtype) a.vector_commutator
    rwa [map_commutator, hVmap, g.first_map] at h
  have hcomm : ⁅V, (a.G1.map G₀.subtype).pCoreIn 2⁆ = otherLine g.E g.s := by
    have h := congrArg (Subgroup.map G₀.subtype) a.local_commutator
    rwa [map_commutator, hVmap, map_pCoreIn_of_injective 2 _ _ G₀.subtype_injective,
      g.singular_map] at h
  let e1 := a.G1.equivMapOfInjective G₀.subtype G₀.subtype_injective
  have hquot : Nonempty ((a.G1.map G₀.subtype ⧸ pCore 2 (a.G1.map G₀.subtype)) ≃*
      Equiv.Perm (Fin 3)) :=
    ⟨(QuotientGroup.congr _ _ e1 (pCore_map_iso 2 e1)).symm.trans a.first_quotient.some⟩
  let eF : a.YF ≃* YE :=
    ((a.YF.equivMapOfInjective G₀.subtype G₀.subtype_injective).trans
      (MulEquiv.subgroupCongr g.first_map)).trans
        ((MulAut.conj g.s⁻¹).subgroupMap YE).symm
  have hcard : Nat.card (YE ⧸ pCore 2 YE) = 3 := by
    let e := (QuotientGroup.congr _ _ eF (pCore_map_iso 2 eF)).symm.trans
      a.first_odd_quotient.some
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_zmod 3
  exact {
    T := g.T, Mc := g.Mc, Y := residualY M g.Mc, E := g.E,
    F := otherLine g.E g.s, YE := YE, YF := YF, XE := lineX g.E,
    TE := lineT g.T g.E, G1 := a.G1.map G₀.subtype, G2 := a.G2.map G₀.subtype,
    Q1 := (a.G1.map G₀.subtype).pCoreIn 2, R := centralizer (V : Set G), s := g.s,
    sylow_le := g.sylow_le, vector_eq := g.vector_eq, residual_eq := rfl,
    residual_image := g.residual_image, ambient_product := g.ambient_product,
    singular_card := g.singular_card, singular := g.singular,
    sylow_stabilizer_eq := rfl,
    first_residual_eq := by
      dsimp [YE, lineY, Stellmacher.twoResidualAmbient]
      rw [intrinsic_twoResidual_eq],
    centralizer_residual_eq := by
      dsimp [lineX, Stellmacher.twoResidualAmbient]
      rw [intrinsic_twoResidual_eq],
    conjugator_mem := g.conjugator_mem,
    conjugator_not_mem := g.conjugator_not_mem, conjugate_plane_eq := rfl,
    conjugate_residual_eq := rfl, residual_product := g.residual_product,
    first_local_eq := hG1, second_local_eq := hG2, generated_eq := hgen,
    first_core_eq := rfl, centralizer_eq := rfl,
    sylow_centralizer_eq := (inf_eq_right.mpr (g.centralizer_le.trans inf_le_left)).symm,
    residual_core_le := g.residual_core_le, first_residual_quotient_card := hcard,
    first_local_quotient := hquot, second_residual_normalized := hnorm,
    first_residual_normalized := g.residual_normalized,
    local_sylow := ⟨a.T, g.sylow_map⟩, vector_le := g.vector_le,
    first_commutator := g.first_commutator, second_commutator := hsecond,
    thompson_le := hYF, local_core_bound := hcore, local_commutator := hcomm }

variable [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]

/-- Recognition from aligned earlier local geometry and the literal source
classification witnesses. The marked configuration is constructed, and no
Thompson residual, surviving quotient or coordinate witness is an input. -/
theorem exists_coordinates_and_planes
    (hF : FSource.Alternative (a.G1.map coreProjection) (a.G2.map coreProjection)
        a.quotientSylow ∨
      FSource.Alternative (a.G2.map coreProjection) (a.G1.map coreProjection)
        a.quotientSylow)
    (hB : Intersection.SourceFFAlternative a.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup G₀).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    ∃ c : HexacodeCoordinates (V.subgroupOf G₀)
        a.centralizer_isTwoGroup a.core_centralizes,
      ∀ i : OrthogonalPlaneIndex, Representation.Hexacode.IsFullWeightScalarPlane
        ((planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)).map
          c.vectors.toLinearMap) := by
  have h := a.source_nonS3_cases_of_classifications hF hB hnot
  obtain ⟨c⟩ := (a.toActionInput h.residual).nonempty_coordinates_of_surviving_source
    h.quotient hB
  exact ⟨c, MarkedPlane.localPlane_isFullWeightScalarPlane c (g.configuration h.first_le)⟩

/-- Full classifiers specialized to the actual SQTK local group give the
coordinates and its two specific definite planes in the non-S₃ branch. -/
theorem exists_coordinates_and_planes_of_full_classifications
    {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup G₀).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    ∃ c : HexacodeCoordinates (V.subgroupOf G₀)
        a.centralizer_isTwoGroup a.core_centralizes,
      ∀ i : OrthogonalPlaneIndex, Representation.Hexacode.IsFullWeightScalarPlane
        ((planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)).map
          c.vectors.toLinearMap) :=
  g.exists_coordinates_and_planes (a.full_goldschmidt_alternative hG₀ classificationF)
    (a.full_sourceFF_alternative hG₀ classificationB) hnot

omit [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))] in
/-- The same source implication with the elementary structure of the actual
normal-closure module constructed from the earlier geometry and core bounds. -/
theorem recognize {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup G₀).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    let _ := g.moduleClosure_elementary
    ∃ c : HexacodeCoordinates (V.subgroupOf G₀)
        a.centralizer_isTwoGroup a.core_centralizes,
      ∀ i : OrthogonalPlaneIndex, Representation.Hexacode.IsFullWeightScalarPlane
        ((planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)).map
          c.vectors.toLinearMap) := by
  let _ := g.moduleClosure_elementary
  exact g.exists_coordinates_and_planes_of_full_classifications
    hG₀ classificationF classificationB hnot

end EarlierGeometry
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction

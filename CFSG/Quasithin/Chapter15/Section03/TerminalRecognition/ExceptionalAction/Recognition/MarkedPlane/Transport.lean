module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.Configuration

/-!
# Transport of the terminal marking

Coordinates carry the actual ambient subgroups into the hexacode, and the
actor map is the composite of the actual quotient map and the coordinate
isomorphism. Normalizing a subgroup of `V` is equivalent to stabilizing its
coordinate subspace. Centralization gives pointwise fixation. Consequently
the source `Y_F` has even image and its two-core fixes the actual image of
`V`, with no identification of a preferred model plane.

The two totally singular source planes must remain separate from the definite
planes: total singularity implies trivial intersection with either definite
summand. This follows directly from the supported-coordinate description.

`ScalarActionOn` specifies a further intermediate conclusion about the
external action of `Y_E`. Its ambient conjugation formula is meaningful even
though `Y_E` need not lie in `G₀`. This module does not prove that conclusion,
scalar invariance of the marked plane, or its Hamming-weight property.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, the
decomposition on printed pp.1121–1122 and the terminal construction and proof
on pp.1152–1155. See `Configuration` for the precise earlier input clauses.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane

variable {G : Type*} [Group G] {G₀ M V E : Subgroup G}
  {d : NaturalOrthogonalAction M V}

/-- A totally singular subgroup contains no nonidentity vector of either
specified definite summand. -/
theorem singular_disjoint_plane (hE : IsSingularIn M V E d) (i : OrthogonalPlaneIndex) :
    Disjoint E (d.plane i) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx, ⟨v, hv, rfl⟩⟩
  change (v : G) = 1
  have hvone : d.coordinates v = 1 := by
    funext j
    obtain ⟨k, hk⟩ := exists_ne i
    exact (hE.2 v hx j k).mpr (hv k hk)
  exact congrArg V.subtype (d.coordinates.injective (hvone.trans d.coordinates.map_one.symm))

namespace SourceConfiguration

variable (cfg : SourceConfiguration G₀ M V d)

/-- The source residual is contained in the original local group `M`. -/
theorem residual_le : cfg.Y ≤ M :=
  le_sup_left.trans cfg.ambient_product.ge

/-- The first residual is a subgroup of the actual source `Y`. -/
theorem first_residual_le : cfg.YE ≤ cfg.Y := by
  rw [cfg.first_residual_eq]
  exact (map_subtype_le _).trans inf_le_left

/-- The second local residual is contained in `G₀`, by its defining generators. -/
theorem second_residual_le : cfg.YF ≤ G₀ :=
  (le_sup_left.trans cfg.first_local_eq.ge).trans (le_sup_left.trans cfg.generated_eq.ge)

/-- The common Sylow subgroup is contained in `G₀`, by its defining generators. -/
theorem sylow_part_le : cfg.TE ≤ G₀ :=
  (le_sup_right.trans cfg.first_local_eq.ge).trans (le_sup_left.trans cfg.generated_eq.ge)

end SourceConfiguration

variable [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]
  {hC : IsPGroup 2 (centralizer (V.subgroupOf G₀ : Set G₀))}
  {hcore : pCore 2 G₀ ≤ centralizer (V.subgroupOf G₀ : Set G₀)}
  (c : HexacodeCoordinates (V.subgroupOf G₀) hC hcore)

/-- The image of a specified ambient subgroup, restricted to the actual module. -/
noncomputable def vectorImage (P : Subgroup G) : Submodule (ZMod 2) Atlas.Codes.hexacode :=
  (planeSubspace (V.subgroupOf G₀) (P.subgroupOf G₀)).map c.vectors.toLinearMap

/-- The actual quotient map followed by the actor coordinates. -/
noncomputable def actorHom : G₀ →* Atlas.Codes.HexAutomorphisms :=
  c.actor.toMonoidHom.comp coreProjection

/-- The image of an ambient actor subgroup after restriction to `G₀`. -/
noncomputable def actorImage (A : Subgroup G) : Subgroup Atlas.Codes.HexAutomorphisms :=
  (A.subgroupOf G₀).map (actorHom c)

/-- A codeword viewed as an element of the original ambient group. -/
noncomputable def ambientVector (w : Atlas.Codes.hexacode) : G :=
  (((c.vectors.symm w).toMul : G₀) : G)

/-- Forgetting the two subgroup inclusions loses no vector information. -/
theorem ambientVector_injective : Function.Injective (ambientVector c) := by
  intro u v h
  apply c.vectors.symm.injective
  apply Additive.toMul.injective
  exact Subtype.ext (Subtype.ext h)

/-- Subspace membership retains the literal ambient subgroup marking. -/
theorem mem_vectorImage (P : Subgroup G) (w : Atlas.Codes.hexacode) :
    w ∈ vectorImage c P ↔ ambientVector c w ∈ P := by
  rw [vectorImage, Submodule.mem_map_equiv]
  rfl

/-- The named image of a definite plane is exactly the expression in the
recognition target, not a newly chosen plane. -/
theorem vectorImage_plane (i : OrthogonalPlaneIndex) :
    vectorImage c (d.plane i) =
      (planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)).map c.vectors.toLinearMap := rfl

/-- Containment of ambient subgroups is respected by vector coordinates. -/
theorem vectorImage_mono {P Q : Subgroup G} (h : P ≤ Q) :
    vectorImage c P ≤ vectorImage c Q := by
  intro w hw
  exact (mem_vectorImage c Q w).mpr (h ((mem_vectorImage c P w).mp hw))

/-- Containment of ambient actors is respected by their actual image. -/
theorem actorImage_mono {A B : Subgroup G} (h : A ≤ B) :
    actorImage c A ≤ actorImage c B :=
  map_mono (fun _ hx => h hx)

/-- The code action agrees with conjugation in the original ambient group. -/
theorem ambientVector_action (g : G₀) (w : Atlas.Codes.hexacode) :
    ambientVector c (Representation.Hexacode.action (actorHom c g) w) =
      (g : G) * ambientVector c w * (g : G)⁻¹ := by
  have he : c.vectors.symm (Representation.Hexacode.action (actorHom c g) w) =
      quotientAction (V.subgroupOf G₀) hC hcore (coreProjection g) (c.vectors.symm w) := by
    apply c.vectors.injective
    rw [c.vectors.apply_symm_apply, c.equivariant, c.vectors.apply_symm_apply]
    rfl
  unfold ambientVector
  rw [he]
  exact quotientAction_ambient_apply G₀ V hC hcore g (c.vectors.symm w)

/-- The intermediate scalar-identification conclusion for an external actor.
Its proof, in particular for `Y_E`, is a separate recognition obligation. -/
def ScalarActionOn (A : Subgroup G) : Prop :=
  ∀ y ∈ A, ∃ k : Fin 3, ∀ w : Atlas.Codes.hexacode,
    y * ambientVector c w * y⁻¹ =
      ambientVector c (Representation.Hexacode.action (Atlas.Codes.hexZ ^ k.val) w)

open Representation.BinaryOffender Representation.NormalElementaryQuotient

/-- Stabilization of the coordinate subspace is precisely ambient normalization
of the original subgroup, for subgroups of the source `V`. -/
theorem actor_stabilizer_iff (P : Subgroup G) (hPV : P ≤ V) (hV : V ≤ G₀) (g : G₀) :
    actorHom c g ∈ subspaceStabilizer Representation.Hexacode.action (vectorImage c P) ↔
      (g : G) ∈ normalizer (P : Set G) := by
  change c.actor (coreProjection g) ∈ subspaceStabilizer Representation.Hexacode.action
    ((planeSubspace (V.subgroupOf G₀) (P.subgroupOf G₀)).map c.vectors.toLinearMap) ↔ _
  rw [← mem_subspaceStabilizer_equivariant (quotientAction (V.subgroupOf G₀) hC hcore)
    Representation.Hexacode.action c.actor c.vectors c.equivariant]
  have hP : P.subgroupOf G₀ ≤ moduleClosure (V.subgroupOf G₀) :=
    fun _ hx => le_normalClosure (hPV hx)
  have he := stabilizer_comap (moduleClosure (V.subgroupOf G₀)) coreProjection
    (QuotientGroup.mk'_surjective _) (coreProjection_ker (V.subgroupOf G₀) hC hcore)
    ((P.subgroupOf G₀).subgroupOf (moduleClosure (V.subgroupOf G₀)))
  rw [map_subgroupOf_eq_of_le hP] at he
  change g ∈ (subspaceStabilizer _ _).comap coreProjection ↔ _
  unfold quotientAction planeSubspace
  rw [he, ← subgroupOf_normalizer_eq (hPV.trans hV)]
  rfl

/-- The source inclusion `Y_F ≤ J(G₀)` puts its actual image in the even cover. -/
theorem actorImage_even (cfg : SourceConfiguration G₀ M V d) :
    actorImage c cfg.YF ≤ Atlas.Codes.hexSign.ker := by
  rintro _ ⟨g, hg, rfl⟩
  rw [← c.thompson_image]
  exact mem_map_of_mem _ (mem_map_of_mem _ (cfg.thompson_le hg))

/-- Ambient centralization transports to pointwise fixation in coordinates. -/
theorem actorImage_fixed (A P : Subgroup G) (hAP : A ≤ centralizer (P : Set G)) :
    vectorImage c P ≤ fixedSpace Representation.Hexacode.action (actorImage c A) := by
  rintro w ⟨v, hv, rfl⟩ ⟨a, ha⟩
  obtain ⟨g, hg, rfl⟩ := ha
  change Representation.Hexacode.action (c.actor (coreProjection g)) (c.vectors v) =
    c.vectors v
  rw [← c.equivariant]
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [quotientAction_ambient_apply]
  exact mul_inv_eq_iff_eq_mul.mpr ((hAP hg) _ hv).symm

/-- The actual two-core of `Y_F` fixes the marked four-dimensional space. -/
theorem source_core_fixed (cfg : SourceConfiguration G₀ M V d) :
    vectorImage c V ≤ fixedSpace Representation.Hexacode.action
      (actorImage c (cfg.YF.pCoreIn 2)) := by
  apply actorImage_fixed
  rw [← cfg.centralizer_eq]
  exact le_sup_right.trans cfg.local_core_bound

variable [Finite G]

/-- The specific definite plane still has binary dimension two in coordinates. -/
theorem vectorImage_plane_finrank (cfg : SourceConfiguration G₀ M V d)
    (i : OrthogonalPlaneIndex) :
    Module.finrank (ZMod 2) (vectorImage c (d.plane i)) = 2 :=
  localPlaneSubspace_map_finrank G₀ M V d cfg.vector_le i c.vectors

/-- The actual source vector group still has binary dimension four. -/
theorem vectorImage_vector_finrank (cfg : SourceConfiguration G₀ M V d) :
    Module.finrank (ZMod 2) (vectorImage c V) = 4 := by
  rw [vectorImage, c.vectors.finrank_map_eq]
  exact localVectorSubspace_finrank G₀ M V d cfg.vector_le

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
